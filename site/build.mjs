#!/usr/bin/env node
// Builds the website (issue #58, docs/design/website.md) into _site/ at the repository root:
//
//   _site/index.html, style.css   the landing page; its examples (landingExamples in examples.mjs) are
//                                 site/example*.hgn, highlighted by the compiler (`hugin highlight`), and
//                                 their outputs site/example*.check, which must equal what `hugin run`
//                                 prints (GoldenTests checks them too)
//   _site/install/                how to install Hugin
//   every page                    the theme switch, site/theme.js, inlined into the <head>; the CSS and
//                                 JS references carry ?v=<content hash> (cache busting)
//   _site/play/                   the playground: play.js (CodeMirror and the page, bundled by esbuild),
//                                 worker.js, hugin.js (the Scala.js compiler, batch W4) and examples.json
//   _site/reference/              the language reference (the mdBook output, reference/book)
//   _site/<old path>.html         a redirect page for every page of the reference at its old URL
//   _site/404.html                the reference's 404 page
//
// Usage (from anywhere): `npm ci --prefix site && node site/build.mjs`, after `sbt stage` and
// `mdbook build reference`. Environment: HUGIN (the launcher, default target/universal/stage/bin/hugin),
// HUGIN_JS (the linked compiler bundle; without it the playground says the compiler is not available),
// BOOK (default reference/book), OUT (default _site). See CONTRIBUTING.md, "The website".
import fs from "node:fs";
import path from "node:path";
import zlib from "node:zlib";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { fileURLToPath } from "node:url";
import { collectExamples, landingExamples } from "./examples.mjs";

const site = path.dirname(fileURLToPath(import.meta.url));
const root = path.dirname(site);
const fromRoot = (p) => path.resolve(root, p);
const hugin = fromRoot(process.env.HUGIN || "target/universal/stage/bin/hugin");
const book = fromRoot(process.env.BOOK || "reference/book");
const bundle = process.env.HUGIN_JS ? fromRoot(process.env.HUGIN_JS) : null;
const out = fromRoot(process.env.OUT || "_site");

function fail(message) {
  console.error(`site/build.mjs: ${message}`);
  process.exit(1);
}

function compiler(args, input) {
  try {
    return execFileSync(hugin, args, { cwd: root, input, encoding: "utf8", stdio: ["pipe", "pipe", "pipe"] });
  } catch (e) {
    fail(`\`hugin ${args.join(" ")}\` failed:\n${e.stderr || e.message}`);
  }
}

const escape = (s) => s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");

// --- the pages: the theme switch (site/theme.js) and the landing page's examples ---------------------
const THEME_BUTTON = `<button class="theme" type="button" aria-label="Switch between light and dark" title="Light or dark">\
<svg class="moon" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M21 12.8A9 9 0 1 1 11.2 3a7 7 0 0 0 9.8 9.8z"/></svg>\
<svg class="sun" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="12" r="4"/><path d="M12 2v2M12 20v2M4.9 4.9l1.4 1.4M17.7 17.7l1.4 1.4M2 12h2M20 12h2M4.9 19.1l1.4-1.4M17.7 6.3l1.4-1.4"/></svg>\
</button>`;

// a page of the site (site/<rel>) with its slots filled: `<!-- build.mjs: theme -->` (the inline script),
// `<!-- build.mjs: theme button -->` and the given extra slots
function page(rel, extra = []) {
  let html = fs.readFileSync(path.join(site, rel), "utf8");
  const theme = fs.readFileSync(path.join(site, "theme.js"), "utf8").replace(/^\/\/.*\n/gm, "").trim();
  const slots = [
    [/<!-- build\.mjs: theme -->/, `<script>${theme}</script>`],
    [/<!-- build\.mjs: theme button -->/, THEME_BUTTON],
    ...extra,
  ];
  for (const [slot, text] of slots) {
    if (!slot.test(html)) fail(`site/${rel} has no slot ${slot}`);
    html = html.replace(slot, () => text);
  }
  write(rel, html);
}

// one example of the landing page: highlighted by the compiler, with the output of `hugin run`, which
// must equal its .check file
function example({ id, file, name, topic }) {
  const code = fs.readFileSync(path.join(site, file + ".hgn"), "utf8");
  const expected = fs.readFileSync(path.join(site, file + ".check"), "utf8");
  const actual = compiler(["run", `site/${file}.hgn`, "--no-color"]);
  if (actual !== expected) fail(`the output of \`hugin run site/${file}.hgn\` differs from site/${file}.check:\n${actual}`);
  const [runs] = JSON.parse(compiler(["highlight"], JSON.stringify([{ code, prelude: true }])));
  if (runs.map((r) => r[0]).join("") !== code) fail(`the highlighted runs do not cover site/${file}.hgn`);
  const spans = runs.map(([text, classes]) =>
    classes.length ? `<span class="${classes.map((c) => "hg-" + c).join(" ")}">${escape(text)}</span>` : escape(text));
  return `<section class="panel" id="${id}" aria-label="${name}">
<pre><code class="hugin">${spans.join("").replace(/\n$/, "")}</code></pre>
<div class="out">
<div class="card-head"><span class="file">$ hugin run ${name}</span><span>output</span></div>
<pre><code>${escape(expected.replace(/\n$/, ""))}</code></pre>
</div>
<div class="card-foot"><span>${escape(topic)}</span><a href="play/#example=${id}">Open in the playground</a></div>
</section>`;
}

// the code card of the landing page: one tab per example, switched by radio buttons (CSS only)
function examples() {
  const radios = landingExamples.map((e, i) =>
    `<input type="radio" name="example" id="tab-${e.id}" aria-controls="${e.id}"${i ? "" : " checked"}>`);
  const labels = landingExamples.map((e) => `<label for="tab-${e.id}">${e.name}</label>`);
  return `<figure class="card examples">
${radios.join("\n")}
<div class="card-head"><div class="ex-tabs">${labels.join("")}</div><span>example</span></div>
<div class="panels">
${landingExamples.map(example).join("\n")}
</div>
</figure>`;
}

function pages() {
  if (!fs.existsSync(hugin)) fail(`no Hugin compiler at ${hugin}: run \`sbt stage\` or set HUGIN`);
  page("index.html", [[/<!-- build\.mjs: examples[^>]*-->/, examples()]]);
  page("install/index.html");
  copy(path.join(site, "style.css"), "style.css");
}

// --- the playground --------------------------------------------------------------------------------
async function playground() {
  let esbuild;
  try {
    esbuild = await import("esbuild");
  } catch (_) {
    fail("esbuild is missing: run `npm ci --prefix site` first");
  }
  await esbuild.build({
    entryPoints: [path.join(site, "play", "main.js")],
    outfile: path.join(out, "play", "play.js"),
    bundle: true, minify: true, format: "esm", target: "es2022", legalComments: "none", logLevel: "warning",
  });
  page("play/index.html");
  copy(path.join(site, "play", "worker.js"), "play/worker.js");
  copy(path.join(site, "play", "play.css"), "play/play.css");
  write("play/examples.json", JSON.stringify(collectExamples(root)));
  // without the linker's source map comment: the map is not published
  if (bundle) write("play/hugin.js", fs.readFileSync(bundle, "utf8").replace(/\n\/\/# sourceMappingURL=\S+\s*$/, "\n"));
  else console.warn("site/build.mjs: HUGIN_JS is not set; the playground is built without the compiler");
}

// --- the reference and the redirects from its old URLs ---------------------------------------------
function htmlFiles(dir, prefix = "") {
  return fs.readdirSync(dir, { withFileTypes: true }).flatMap((e) =>
    e.isDirectory() ? htmlFiles(path.join(dir, e.name), prefix + e.name + "/")
      : e.name.endsWith(".html") ? [prefix + e.name] : []);
}

function redirect(page) {
  const target = "../".repeat(page.split("/").length - 1) + "reference/" + page;
  return `<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Moved: The Hugin Reference</title>
<meta name="robots" content="noindex">
<link rel="canonical" href="${target}">
<meta http-equiv="refresh" content="0; url=${target}">
</head>
<body>
<p>This page of the reference has moved to <a href="${target}">${target}</a>.</p>
</body>
</html>
`;
}

function reference() {
  if (!fs.existsSync(path.join(book, "index.html"))) fail(`no book at ${book}: run \`mdbook build reference\``);
  fs.cpSync(book, path.join(out, "reference"), { recursive: true });
  copy(path.join(book, "404.html"), "404.html");
  let count = 0;
  for (const page of htmlFiles(book)) {
    if (page === "index.html" || page === "404.html") continue; // the landing page and the site's 404
    if (fs.existsSync(path.join(out, page))) fail(`the redirect for ${page} would overwrite a page of the site`);
    write(page, redirect(page));
    count++;
  }
  return count;
}

// --- cache busting -----------------------------------------------------------------------------------
// The assets keep their names, and browsers and the CDN cache them (GitHub Pages: max-age=600; phones keep
// them longer), so a page could be rendered with the style sheet of an earlier version. Every reference to
// a CSS or JS file of the site (and to examples.json) gets `?v=<hash of the file's content>`, innermost
// first: hugin.js in worker.js, worker.js and examples.json in play.js, then the pages' style sheets and
// scripts. A new version of a file thus has a new URL; an unchanged one stays cached.
const hash = (rel) => createHash("sha256").update(fs.readFileSync(path.join(out, rel))).digest("hex").slice(0, 10);

function bust(rel, refs) {
  const file = path.join(out, rel);
  let text = fs.readFileSync(file, "utf8");
  for (const [quoted, target] of refs) {
    if (!fs.existsSync(path.join(out, target))) continue; // e.g. no compiler bundle
    if (!text.includes(quoted)) fail(`${rel} has no reference ${quoted} to version`);
    text = text.split(quoted).join(quoted.replace(/(["'])$/, `?v=${hash(target)}$1`));
  }
  fs.writeFileSync(file, text);
}

function cacheBusting() {
  bust("play/worker.js", [['"hugin.js"', "play/hugin.js"]]);
  bust("play/play.js", [['"worker.js"', "play/worker.js"], ['"examples.json"', "play/examples.json"]]);
  bust("index.html", [['href="style.css"', "style.css"]]);
  bust("install/index.html", [['href="../style.css"', "style.css"]]);
  bust("play/index.html", [['href="../style.css"', "style.css"], ['href="play.css"', "play/play.css"], ['src="play.js"', "play/play.js"]]);
}

// --- helpers ---------------------------------------------------------------------------------------
function write(rel, text) {
  fs.mkdirSync(path.dirname(path.join(out, rel)), { recursive: true });
  fs.writeFileSync(path.join(out, rel), text);
}

function copy(from, rel) {
  fs.mkdirSync(path.dirname(path.join(out, rel)), { recursive: true });
  fs.copyFileSync(from, path.join(out, rel));
}

const gzip = (...rels) =>
  (rels.reduce((n, r) => n + zlib.gzipSync(fs.readFileSync(path.join(out, r)), { level: 9 }).length, 0) / 1024).toFixed(1);

fs.rmSync(out, { recursive: true, force: true });
pages();
await playground();
cacheBusting();
const redirects = reference();
console.log(`site/build.mjs: wrote ${path.relative(root, out) || out}/`);
console.log(`  landing page ${gzip("index.html", "style.css")} KB gzip (HTML and CSS; JavaScript only for the theme switch)`);
console.log(`  playground   ${gzip("play/play.js")} KB gzip (editor and page)` +
  (bundle ? `, compiler ${gzip("play/hugin.js")} KB gzip` : ", no compiler bundle"));
console.log(`  reference    ${redirects} redirect pages from the old URLs`);
