// A lesson of the language tour (site/build.mjs, site/tour/lessons.mjs). The page is complete without
// JavaScript: the lesson's text, its program (highlighted by the compiler) and the result that CI checked
// (TourExamplesSuite). This script makes the program editable with the playground's editor
// (site/play/editor.js) and checks it in the browser with the playground's compiler worker
// (site/play/worker.js, which loads the same hugin.js). The worker is started lazily, when the reader first
// focuses or edits the program or presses a button, and once per page; the browser caches hugin.js across
// lessons. After a pause in typing the program is run; the result pane shows the diagnostics, or the
// theorems that were checked (the names of the program's %opaque directives, with their types) and the
// output. Back and Next are also ← and → outside the editor.
import { createEditor, showDiagnostics, showTokens, clear, setProgram, offset, applySuggestion } from "../play/editor.js";
import { h, counts, diagnostics } from "../play/results.js";
import { showInfo } from "../play/ide.js";
import { showHints } from "../play/hints.js";
import { encodeProgram } from "../play/share.js";
import { EditorView } from "@codemirror/view";

const BUDGET_MS = 30_000; // the standard library's semantics take a while to load in the browser
const IDLE_MS = 600;
const root = document.body.dataset.root || "";
document.documentElement.classList.add("js");
const data = JSON.parse(document.getElementById("lesson").textContent);
const $ = (sel) => document.querySelector(sel);
const ui = { editor: $("[data-editor]"), tools: $("[data-tools]"), status: $("[data-status]"), result: $("[data-result]") };

// --- the compiler worker, started on first use ---------------------------------------------------
let worker = null, ready = null, available = false, nextId = 1;
const pending = new Map();

function startWorker() {
  if (worker) return ready;
  worker = new Worker(new URL(root + "play/worker.js", location.href));
  ready = new Promise((resolve) => {
    worker.onmessage = (e) => {
      if ("ready" in e.data) { available = e.data.ready; return resolve(e.data); }
      const p = pending.get(e.data.id);
      if (!p) return;
      pending.delete(e.data.id); clearTimeout(p.timer);
      e.data.error ? p.reject(new Error(e.data.error)) : p.resolve(e.data.result);
    };
    worker.onerror = (e) => { e.preventDefault(); resolve({ ready: false, error: e.message || "the worker failed" }); };
  });
  return ready;
}

function stopWorker(reason) {
  worker.terminate();
  worker = null;
  for (const p of pending.values()) { clearTimeout(p.timer); p.reject(Object.assign(new Error(reason), { stopped: true })); }
  pending.clear();
}

function request(op, source, extra = {}) {
  return new Promise((resolve, reject) => {
    const id = nextId++;
    const timer = setTimeout(() => stopWorker(`stopped after ${BUDGET_MS / 1000} s`), BUDGET_MS);
    pending.set(id, { resolve, reject, timer });
    worker.postMessage({ id, op, version, source, printAfter: "", ...extra });
  });
}

// --- checking ------------------------------------------------------------------------------------
let version = 0, busy = false, again = false, timer = null;

function status(text, kind = "") {
  ui.status.textContent = text;
  ui.status.className = "status" + (kind ? " " + kind : "");
}

// the theorems of the program: the names that its %opaque directives list, with their types from the
// annotation table (the hover of the name's declaration)
function theorems(source, info) {
  const names = [...source.matchAll(/^\s*%opaque\s+([^.]*)\./gm)].flatMap((m) => m[1].trim().split(/\s+/)).filter(Boolean);
  const hovers = (info && info.hovers) || [];
  return names.map((name) => {
    const decl = ((info && info.names) || []).find(([from, to, hover, , flags]) =>
      (flags & 1) && hover != null && source.slice(from, to) === name);
    const signature = decl ? hovers[decl[2]] && hovers[decl[2]][0] : null;
    return { name, signature };
  });
}

function render(result, source, ms) {
  const errors = result.diagnostics.filter((d) => d.level === "error");
  const goto = (span) => {
    const at = offset(editor.state.doc, span.start);
    editor.dispatch({ selection: { anchor: at }, effects: EditorView.scrollIntoView(at, { y: "center" }) });
    editor.focus();
  };
  const parts = [];
  if (errors.length) {
    parts.push(h("p", { class: "fail" }, `Rejected: ${counts(result.diagnostics)}.`));
    parts.push(diagnostics(result, (s) => applySuggestion(editor, s), goto));
  } else {
    const checked = theorems(source, result.info);
    parts.push(h("p", { class: "ok" }, checked.length ? "No errors. Checked:" : "No errors."));
    if (checked.length)
      parts.push(h("ul", { class: "theorems" }, checked.map((t) =>
        h("li", {}, h("code", {}, t.signature ? t.signature.replace(/^meta (definition|declaration) /, "") : t.name)))));
    if (result.diagnostics.length) parts.push(diagnostics(result, (s) => applySuggestion(editor, s), goto));
    if (result.output.length) parts.push(h("pre", { class: "text" }, result.output.join("\n")));
  }
  ui.result.replaceChildren(...parts.flat(2));
  status(`${errors.length ? "rejected" : "checked"} in your browser, ${ms} ms`, errors.length ? "error" : "");
}

async function check() {
  clearTimeout(timer);
  if (busy) { again = true; return; }
  await startWorker();
  if (!available) return status("the compiler is not available in this build", "error");
  const source = editor.state.doc.toString();
  const asked = version;
  busy = true;
  status("checking…", "busy");
  const started = performance.now();
  try {
    const result = await request("run", source);
    if (asked === version) {
      showDiagnostics(editor, result.diagnostics);
      showTokens(editor, result.tokens);
      showInfo(editor, result.info);
      showHints(editor, result.info && result.info.hints);
      render(result, source, Math.round(performance.now() - started));
    }
  } catch (e) {
    status(e.stopped ? e.message : `the compiler failed: ${e.message}`, "error");
  } finally {
    busy = false;
    if (again || asked !== version) { again = false; checkSoon(); }
  }
}

function checkSoon() {
  clearTimeout(timer);
  timer = setTimeout(check, IDLE_MS);
}

// the editor's completion and actions at the cursor, as in the playground (nothing while a check runs)
async function ask(op, source, extra) {
  if (busy || !available || !worker) return null;
  try {
    const result = await request(op, source, extra);
    return result.version === version ? result : null;
  } catch (_) {
    return null;
  }
}

// --- the page ------------------------------------------------------------------------------------
ui.editor.replaceChildren(); // the static program; the editor is created in place, so that it measures its lines
const editor = createEditor(ui.editor, data.code, {
  onRun: () => check(),
  onEdit: () => { version++; status("edited", "busy"); checkSoon(); },
  complete: (source, at) => ask("complete", source, { offset: at }),
  actions: (source, from, to) => ask("actions", source, { from, to }),
  expansion: () => Promise.resolve(null),
  onExpansion: () => {},
});
ui.editor.classList.add("live");
editor.dom.addEventListener("focusin", () => { if (!worker) check(); }, { once: true });

function load(code, label) {
  setProgram(editor, code);
  clear(editor);
  version++;
  status(label, "busy");
  check();
}

const button = (text, title, onclick) => h("button", { type: "button", class: "fix", title, onclick }, text);
const playground = ui.tools.querySelector("a");
playground.onclick = async (e) => {
  if (editor.state.doc.toString() === data.code) return; // the lesson's own program: #example=
  e.preventDefault();
  location.href = new URL(root + "play/#" + (await encodeProgram(editor.state.doc.toString())), location.href).href;
};
ui.tools.prepend(
  button("Reset", "Restore the lesson's program", () => load(data.code, "reset")),
  ...(data.wrong ? [button("Try a wrong version", "Load a wrong proof and see the compiler reject it", () => load(data.wrong, "a wrong version"))] : []),
);

// ← and → outside the editor and form controls go to the previous and next lesson
document.addEventListener("keydown", (e) => {
  if (e.altKey || e.ctrlKey || e.metaKey || e.shiftKey || e.defaultPrevented) return;
  const t = e.target;
  if (t.closest && t.closest(".cm-editor, input, textarea, select, [contenteditable]")) return;
  const link = document.querySelector(`.pager a[data-key="${e.key}"]`);
  if (link) location.href = link.href;
});
