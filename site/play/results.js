// The results pane: answers and `%output` relations as tables, the diagnostics, and the text the CLI
// would print (docs/design/website.md 4.8). Plain DOM, no framework.
import { mainSpan } from "./editor.js";

export function h(tag, attrs = {}, ...children) {
  const el = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (k.startsWith("on")) el[k] = v;
    else if (v != null && v !== false) el.setAttribute(k, v === true ? "" : v);
  }
  el.append(...children.flat(Infinity).filter((c) => c != null && c !== false));
  return el;
}

function table(vars, rows) {
  if (!vars.length) return h("p", { class: "empty" }, rows.length ? "true" : "false");
  return h("table", {},
    h("thead", {}, h("tr", {}, vars.map((v) => h("th", {}, v)))),
    h("tbody", {}, rows.map((r) => h("tr", {}, r.map((c) => h("td", {}, String(c)))))));
}

function answers(result) {
  if (result.answers.length)
    return result.answers.map((a) => [h("p", { class: "query" }, a.query), table(a.vars, a.rows)]);
  if (result.output.length) return h("pre", { class: "text" }, result.output.join("\n"));
  return h("p", { class: "empty" }, "No queries.");
}

function relations(result) {
  if (!result.relations.length) return h("p", { class: "empty" }, "No %output relations.");
  return result.relations.map((r) => [h("p", { class: "query" }, r.name), table(r.vars, r.rows)]);
}

function diagnostics(result, onFix, onGoto) {
  if (!result.diagnostics.length) return h("p", { class: "empty" }, "No diagnostics.");
  return result.diagnostics.map((d) => {
    const span = mainSpan(d);
    const level = d.level === "error" ? "error" : "warning";
    return h("div", { class: "diag " + level },
      h("span", { class: "code" }, `${d.level}${d.code && d.code.id ? `[${d.code.id}]` : ""}`),
      " ",
      span ? h("a", { href: "#", onclick: (e) => (e.preventDefault(), onGoto(span)) }, `line ${span.start.line}`) : null,
      span ? ": " : "",
      d.message,
      d.code && d.code.url ? [" · ", h("a", { href: d.code.url, target: "_blank", rel: "noopener" }, "explanation")] : null,
      (d.suggestions || []).map((s) => [" · ", h("button", { type: "button", class: "fix", onclick: () => onFix(s) }, s.message)]));
  });
}

function text(result) {
  const parts = [...result.diagnostics.map((d) => d.rendered || d.message), result.output.join("\n")];
  const body = parts.filter((p) => p).join("\n");
  return h("pre", { class: "text" }, body || "(no output)");
}

export function counts(diags) {
  const e = diags.filter((d) => d.level === "error").length;
  const w = diags.filter((d) => d.level === "warning").length;
  const plural = (n, s) => `${n} ${s}${n === 1 ? "" : "s"}`;
  return [e ? plural(e, "error") : "", w ? plural(w, "warning") : ""].filter(Boolean).join(", ");
}

// the tabs and their contents for a result; `printed` adds a tab with the program after a phase
export function views(result, { onFix, onGoto, phase }) {
  const n = result.diagnostics.length;
  const tabs = [
    ["answers", "Answers", () => answers(result)],
    ["diagnostics", `Diagnostics${n ? ` (${n})` : ""}`, () => diagnostics(result, onFix, onGoto)],
    ["relations", "Relations", () => relations(result)],
    ["text", "Text", () => text(result)],
  ];
  if (result.printed !== undefined)
    tabs.push(["printed", `After ${phase}`, () => h("pre", { class: "text hugin" }, result.printed)]);
  return tabs;
}
