#!/usr/bin/env node
// Smoke test of the hovers and definitions of the reference's code blocks (issue #132,
// docs/design/web-ide.md, 7 and 9) in Chromium, with Playwright: mouse hover, the keyboard model (one tab
// stop per block, arrow keys between names, Enter, Escape, Tab), the touch tap and the definition links,
// in a desktop window, a 390 px wide one and on a 390 px wide touch screen, in a light and a dark theme.
// Run in CI after `mdbook build reference` (.github/workflows/reference.yml).
//
// Usage: node reference/hugin-info-smoke.cjs [<book dir, default reference/book>] [<screenshot dir>]
// It needs the `playwright` package (NODE_PATH may point at its node_modules) and its Chromium.
"use strict";
const path = require("node:path");
const fs = require("node:fs");
const { pathToFileURL } = require("node:url");
const { chromium } = require("playwright");

const book = path.resolve(process.argv[2] || path.join(__dirname, "book"));
const shots = process.argv[3] ? path.resolve(process.argv[3]) : null;
const page = (rel) => pathToFileURL(path.join(book, rel)).href;
const POPUP = "#hg-popup:not([hidden])";
let failures = 0;

function check(ok, what) {
  console.log(`${ok ? "ok  " : "FAIL"} ${what}`);
  if (!ok) failures++;
}

async function shot(p, name) {
  if (!shots) return;
  fs.mkdirSync(shots, { recursive: true });
  await p.waitForTimeout(250); // the popup's fade
  await p.screenshot({ path: path.join(shots, `${name}.png`) });
}

const active = (p) =>
  p.evaluate(() => {
    const e = document.activeElement;
    const block = e && e.closest("code[data-hg]");
    return { tag: e.tagName, id: e.id, i: e.getAttribute("data-i"), text: e.textContent, inBlock: !!block, isBlock: e.matches("code[data-hg]") };
  });
const popupText = (p) => p.evaluate(() => document.getElementById("hg-popup").textContent);

// mouse and keyboard, in a desktop window and in a narrow one
async function desktop(browser, theme, width) {
  const ctx = await browser.newContext({ viewport: { width, height: 800 } });
  await ctx.addInitScript((t) => localStorage.setItem("mdbook-theme", JSON.stringify(t)), theme);
  const p = await ctx.newPage();
  const errors = [];
  p.on("pageerror", (e) => errors.push(e.message));
  await p.goto(page("object/rules.html"));
  check((await p.locator("code[data-hg]").count()) > 0, `${theme} ${width}px: rules.html has interactive blocks`);
  check((await p.locator("script#hg-hovers").count()) === 1, `${theme} ${width}px: one hover table`);

  // mouse
  const use = p.locator('code[data-hg] a[data-i][href^="#"]').first();
  await use.scrollIntoViewIfNeeded();
  await use.hover();
  await p.waitForSelector(POPUP, { timeout: 2000 });
  check((await popupText(p)).length > 0, `${theme} ${width}px: hovering a name shows its popup`);
  check((await use.getAttribute("aria-describedby")) === "hg-popup", `${theme} ${width}px: the name points at the popup`);
  check((await p.locator("code[data-hg] .hg-occ").count()) >= 2, `${theme} ${width}px: its occurrences are marked`);
  check((await p.locator(`${POPUP} a.hg-def`).count()) === 1, `${theme} ${width}px: the popup has a Definition link`);
  await shot(p, `desktop${width}-${theme}-hover`);
  await p.mouse.move(5, 5);
  await p.waitForSelector("#hg-popup[hidden]", { state: "attached", timeout: 2000 });
  check(true, `${theme} ${width}px: leaving the name hides the popup`);

  // keyboard
  const url = p.url();
  const block = p.locator("code[data-hg]").first();
  await block.focus();
  await p.keyboard.press("ArrowRight");
  let a = await active(p);
  check(a.inBlock && !a.isBlock, `${theme} ${width}px: ArrowRight focuses the first name (${a.text})`);
  check(await p.locator(POPUP).isVisible(), `${theme} ${width}px: the focused name shows its popup`);
  const first = a.text;
  await p.keyboard.press("ArrowRight");
  a = await active(p);
  check(a.inBlock && a.text.length > 0, `${theme} ${width}px: ArrowRight moves to the next name (${a.text})`);
  await shot(p, `desktop${width}-${theme}-keyboard`);
  await p.keyboard.press("End");
  await p.keyboard.press("Home");
  a = await active(p);
  check(a.text === first, `${theme} ${width}px: Home returns to the first name`);
  await p.keyboard.press("ArrowLeft");
  check(p.url() === url, `${theme} ${width}px: the arrow keys do not turn the page`);
  await p.keyboard.press("Escape");
  a = await active(p);
  check(a.isBlock && !(await p.locator(POPUP).count()), `${theme} ${width}px: Escape hides the popup and returns to the block`);
  // Enter on a use moves to its declaration in the block
  const target = await use.getAttribute("href");
  const owner = use.locator("xpath=ancestor::code[@data-hg]");
  await owner.focus();
  const index = await owner.evaluate((b, u) => Array.from(b.querySelectorAll("[data-i],a[href]")).findIndex((n) => n.getAttribute("href") === u), target);
  await p.keyboard.press("Home");
  for (let k = 0; k < index; k++) await p.keyboard.press("ArrowRight");
  await p.keyboard.press("Enter");
  a = await active(p);
  check("#" + a.id === target, `${theme} ${width}px: Enter on a use moves to its declaration (${target})`);
  await p.keyboard.press("Tab");
  a = await active(p);
  check(!a.inBlock, `${theme} ${width}px: Tab leaves the block`);
  check(!(await p.locator(POPUP).count()), `${theme} ${width}px: leaving the block hides the popup`);

  // a library name links to its module's page, at its row
  const lib = p.locator('code[data-hg] a[href*="std/"]').first();
  const href = await lib.getAttribute("href");
  await lib.click();
  await p.waitForLoadState();
  const hash = new URL(p.url()).hash;
  check(p.url().includes("/std/") && hash.startsWith("#hg-") && (await p.locator(hash).count()) === 1, `${theme} ${width}px: a library name links to its row (${href})`);
  check(errors.length === 0, `${theme} ${width}px: no script errors ${errors.join("; ")}`);
  await ctx.close();
}

async function touch(browser, theme) {
  const ctx = await browser.newContext({ viewport: { width: 390, height: 844 }, deviceScaleFactor: 2, isMobile: true, hasTouch: true });
  await ctx.addInitScript((t) => localStorage.setItem("mdbook-theme", JSON.stringify(t)), theme);
  const p = await ctx.newPage();
  await p.goto(page("object/rules.html"));
  const url = p.url();
  const use = p.locator('code[data-hg] a[data-i][href^="#"]').first();
  await use.scrollIntoViewIfNeeded();
  await use.tap();
  await p.waitForSelector(POPUP, { timeout: 2000 });
  check(p.url() === url, `${theme} touch: the first tap shows the popup instead of following the link`);
  await p.waitForTimeout(800); // the mouse events Chromium sends after a tap do not close it
  check(await p.locator(POPUP).isVisible(), `${theme} touch: the popup stays open`);
  const box = await p.locator("#hg-popup").boundingBox();
  check(box.x >= 0 && box.x + box.width <= 390 - 16, `${theme} touch: the popup fits the viewport (${Math.round(box.x)}+${Math.round(box.width)})`);
  const def = await p.locator(`${POPUP} a.hg-def`).boundingBox();
  check(def && def.height >= 44, `${theme} touch: the Definition link is at least 44 px high`);
  await shot(p, `touch-${theme}-tap`);
  await use.tap();
  check(!(await p.locator(POPUP).count()), `${theme} touch: a second tap on the name closes it`);
  await use.tap();
  await p.locator("h1").first().tap();
  check(!(await p.locator(POPUP).count()), `${theme} touch: a tap outside closes it`);
  await use.tap();
  const href = await use.getAttribute("href");
  await p.locator(`${POPUP} a.hg-def`).tap();
  await p.waitForTimeout(100);
  check(new URL(p.url()).hash === href && !(await p.locator(POPUP).count()), `${theme} touch: the Definition link goes to the declaration (${href})`);
  await ctx.close();
}

(async () => {
  const browser = await chromium.launch();
  try {
    for (const theme of ["light", "navy"]) {
      await desktop(browser, theme, 1280);
      await desktop(browser, theme, 390);
      await touch(browser, theme);
    }
  } finally {
    await browser.close();
  }
  if (failures) {
    console.error(`hugin-info-smoke: ${failures} check(s) failed`);
    process.exit(1);
  }
  console.log("hugin-info-smoke: all checks passed");
})().catch((e) => {
  console.error(e);
  process.exit(1);
});
