#!/usr/bin/env node
// Builds the website (issue #58, docs/design/website.md) into _site/ at the repository root:
//
//   _site/index.html, style.css   the landing page; its example is site/example.hgn, highlighted by the
//                                 compiler (`hugin highlight`), and its output site/example.check, which
//                                 must equal what `hugin run` prints (GoldenTests checks it too)
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
import { fileURLToPath } from "node:url";
import { collectExamples } from "./examples.mjs";

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

// --- the landing page ------------------------------------------------------------------------------
function landing() {
  if (!fs.existsSync(hugin)) fail(`no Hugin compiler at ${hugin}: run \`sbt stage\` or set HUGIN`);
  const code = fs.readFileSync(path.join(site, "example.hgn"), "utf8");
  const expected = fs.readFileSync(path.join(site, "example.check"), "utf8");
  const actual = compiler(["run", "site/example.hgn", "--no-color"]);
  if (actual !== expected)
    fail(`the output of \`hugin run site/example.hgn\` differs from site/example.check:\n${actual}`);
  const [runs] = JSON.parse(compiler(["highlight"], JSON.stringify([{ code, prelude: true }])));
  if (runs.map((r) => r[0]).join("") !== code) fail("the highlighted runs do not cover site/example.hgn");
  const spans = runs.map(([text, classes]) =>
    classes.length ? `<span class="${classes.map((c) => "hg-" + c).join(" ")}">${escape(text)}</span>` : escape(text));
  let page = fs.readFileSync(path.join(site, "index.html"), "utf8");
  const slots = [
    [/<!-- build\.mjs: site\/example\.hgn[^>]*-->/, spans.join("").replace(/\n$/, "")],
    [/<!-- build\.mjs: site\/example\.check[^>]*-->/, escape(expected.replace(/\n$/, ""))],
  ];
  for (const [slot, html] of slots) {
    if (!slot.test(page)) fail(`site/index.html has no slot ${slot}`);
    page = page.replace(slot, () => html);
  }
  write("index.html", page);
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
  copy(path.join(site, "play", "index.html"), "play/index.html");
  copy(path.join(site, "play", "worker.js"), "play/worker.js");
  copy(path.join(site, "play", "play.css"), "play/play.css");
  write("play/examples.json", JSON.stringify(collectExamples(root)));
  if (bundle) copy(bundle, "play/hugin.js");
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
landing();
await playground();
const redirects = reference();
console.log(`site/build.mjs: wrote ${path.relative(root, out) || out}/`);
console.log(`  landing page ${gzip("index.html", "style.css")} KB gzip (HTML and CSS), no JavaScript`);
console.log(`  playground   ${gzip("play/play.js")} KB gzip (editor and page)` +
  (bundle ? `, compiler ${gzip("play/hugin.js")} KB gzip` : ", no compiler bundle"));
console.log(`  reference    ${redirects} redirect pages from the old URLs`);
