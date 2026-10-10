// The playground's examples: the landing page's examples and the reference's checked `hugin,run` blocks
// (ReferenceExamplesSuite compiles and runs them), in the order of reference/src/SUMMARY.md. Blocks with
// input facts or a relative %import are left out: the playground has a single file and no facts.
import fs from "node:fs";
import path from "node:path";

const FENCE = /^```([^\n]*)\n([\s\S]*?)^```[ \t]*$/gm;

function chapters(src) {
  const summary = fs.readFileSync(path.join(src, "SUMMARY.md"), "utf8");
  return [...summary.matchAll(/\[([^\]]+)\]\(([^)]+\.md)\)/g)].map((m) => ({ title: m[1], file: m[2] }));
}

function slug(file) {
  return file.replace(/\.md$/, "").replace(/\/index$/, "").replace(/[^A-Za-z0-9]+/g, "-");
}

function examplesOf(src, { title, file }) {
  const full = path.join(src, file);
  if (!fs.existsSync(full)) return [];
  const text = fs.readFileSync(full, "utf8");
  const blocks = [...text.matchAll(FENCE)];
  const out = [], seen = new Map();
  blocks.forEach((m, i) => {
    const info = m[1].split(/[,\s]+/).filter(Boolean);
    if (info[0] !== "hugin" || !info.includes("run")) return;
    const next = blocks[i + 1];
    if (next && next[1].trim() === "facts") return;
    if (/%import\s+"(?!std\/)/.test(m[2])) return;
    const before = text.slice(0, m.index);
    const heading = [...before.matchAll(/^#{2,4} +(.+)$/gm)].pop();
    let name = heading ? heading[1].replace(/`/g, "").trim() : title;
    const n = (seen.get(name) || 0) + 1;
    seen.set(name, n);
    if (n > 1) name += ` (${n})`;
    out.push({ id: `${slug(file)}-${out.length + 1}`, group: title, title: name, code: m[2] });
  });
  return out;
}

// The examples of the landing page's code card, one tab each: site/<file>.hgn, whose output must equal
// site/<file>.check (GoldenTests runs them as it runs tests/run; site/build.mjs checks the output again).
export const landingExamples = [
  { id: "people", file: "example", name: "people.hgn", topic: "Directives and functors" },
  { id: "routes", file: "example-routes", name: "routes.hgn", topic: "Bound columns" },
  { id: "exprs", file: "example-exprs", name: "exprs.hgn", topic: "First-class facts" },
];

export function collectExamples(root) {
  const src = path.join(root, "reference", "src");
  const landing = landingExamples.map((e) => ({
    id: e.id,
    group: "Home",
    title: `${e.name}: ${e.topic.toLowerCase()}`,
    code: fs.readFileSync(path.join(root, "site", e.file + ".hgn"), "utf8"),
  }));
  return [...landing, ...chapters(src).flatMap((c) => examplesOf(src, c))];
}
