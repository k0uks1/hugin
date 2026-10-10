// The playground (issue #58, docs/design/website.md 4.6-4.10). The compiler runs in a Web Worker
// (worker.js, which loads the Scala.js bundle hugin.js); this page holds the editor, the toolbar and the
// results. Run and Check are explicit; Ctrl-Enter runs. A request that takes longer than the budget
// terminates the worker, which is then restarted (a cold start). Nothing leaves the page.
import { createEditor, showDiagnostics, showTokens, clear, setProgram, offset, applySuggestion } from "./editor.js";
import { views, counts, h } from "./results.js";
import { encodeProgram, readFragment } from "./share.js";
import { EditorView } from "@codemirror/view";

const BUDGET_MS = 10_000;
const $ = (id) => document.getElementById(id);
const ui = {
  run: $("run"), check: $("check"), example: $("example"), phase: $("phase"), status: $("status"),
  share: $("share"), editor: $("editor"), summary: $("summary"), tabs: $("tabs"), body: $("body"),
};

// --- the compiler worker -------------------------------------------------------------------------
let worker, ready, pending = null, nextId = 1;

function startWorker() {
  worker = new Worker("worker.js");
  ready = new Promise((resolve) => {
    worker.onmessage = (e) => {
      if ("ready" in e.data) return resolve(e.data);
      if (pending && e.data.id === pending.id) {
        const p = pending; pending = null; clearTimeout(p.timer);
        e.data.error ? p.reject(new Error(e.data.error)) : p.resolve(e.data.result);
      }
    };
    worker.onerror = (e) => { e.preventDefault(); resolve({ ready: false, error: e.message || "the worker failed" }); };
  });
}

function stopWorker(reason) {
  worker.terminate();
  if (pending) { const p = pending; pending = null; clearTimeout(p.timer); p.reject(Object.assign(new Error(reason), { stopped: true })); }
  startWorker();
  ready.then(onReady);
}

function request(op, source, printAfter) {
  return new Promise((resolve, reject) => {
    const id = nextId++;
    const timer = setTimeout(() => stopWorker(`stopped after ${BUDGET_MS / 1000} s`), BUDGET_MS);
    pending = { id, resolve, reject, timer };
    worker.postMessage({ id, op, source, printAfter });
  });
}

// --- the page --------------------------------------------------------------------------------------
let examples = [], busy = false, available = false, current = null, tab = "answers";

function status(text, kind = "") {
  ui.status.textContent = text;
  ui.status.className = "status" + (kind ? " " + kind : "");
}

function onReady(info) {
  available = info.ready;
  ui.run.disabled = ui.check.disabled = !available;
  if (!available) return status("The compiler is not available in this build.", "error");
  if (ui.phase.options.length === 1)
    for (const p of info.phases || []) ui.phase.append(h("option", { value: p }, `Show after: ${p}`));
  ui.phase.disabled = !(info.phases || []).length;
  if (!busy) status("ready");
}

function renderResult() {
  ui.tabs.replaceChildren(); ui.body.replaceChildren();
  const note = h("p", { class: "note" },
    "The compiler runs in this page (Scala.js, in a Web Worker). Programs are not sent anywhere. ",
    `A run stops after ${BUDGET_MS / 1000} s.`);
  if (!current) return ui.body.append(note);
  const all = views(current, {
    phase: ui.phase.value,
    onFix: (s) => applySuggestion(editor, s),
    onGoto: (span) => {
      const at = offset(editor.state.doc, span.start);
      editor.dispatch({ selection: { anchor: at }, effects: EditorView.scrollIntoView(at, { y: "center" }) });
      editor.focus();
    },
  });
  if (!all.some(([key]) => key === tab)) tab = "answers";
  for (const [key, label, render] of all) {
    const selected = key === tab;
    ui.tabs.append(h("button", { type: "button", role: "tab", "aria-selected": String(selected),
      onclick: () => { tab = key; renderResult(); } }, label));
    if (selected) ui.body.append(...[render()].flat(2));
  }
  ui.body.append(note);
}

async function compile(op) {
  if (busy) return stopWorker("stopped");
  if (!available) return;
  const source = editor.state.doc.toString();
  busy = true;
  ui.run.textContent = "Stop"; ui.check.disabled = true;
  status(op === "run" ? "running…" : "checking…", "busy");
  const started = performance.now();
  try {
    const result = await request(op, source, ui.phase.value);
    const ms = Math.round(performance.now() - started);
    const errors = result.diagnostics.some((d) => d.level === "error");
    current = result;
    if (op === "check" && !result.printed) tab = "diagnostics";
    else if (errors) tab = "diagnostics";
    else if (result.printed !== undefined) tab = "printed";
    else if (tab === "diagnostics" || tab === "printed") tab = "answers";
    if (editor.state.doc.toString() === source) {
      showDiagnostics(editor, result.diagnostics);
      if (!errors) showTokens(editor, result.tokens);
    }
    ui.summary.textContent = counts(result.diagnostics);
    status(`${op === "run" ? "ran" : "checked"} in ${ms} ms`, errors ? "error" : "");
  } catch (e) {
    if (e.stopped) current = null;
    status(e.stopped ? e.message : `the compiler failed: ${e.message}`, "error");
  } finally {
    busy = false;
    ui.run.textContent = "Run"; ui.check.disabled = !available;
    renderResult();
  }
}

function loadExample(id) {
  const ex = examples.find((e) => e.id === id) || examples[0];
  if (!ex) return;
  setProgram(editor, ex.code);
  ui.example.value = ex.id;
}

async function share() {
  const fragment = await encodeProgram(editor.state.doc.toString());
  history.replaceState(null, "", "#" + fragment);
  try {
    await navigator.clipboard.writeText(location.href);
    status("link copied");
  } catch (_) {
    status("link in the address bar");
  }
}

function onEdit() {
  ui.summary.textContent = "";
  if (ui.example.value) ui.example.value = "";
}

const editor = createEditor(ui.editor, "", { onRun: () => compile("run"), onEdit });
startWorker();
ready.then(onReady);

ui.run.onclick = () => compile("run");
ui.check.onclick = () => compile("check");
ui.share.onclick = share;
ui.example.onchange = () => {
  if (!ui.example.value) return;
  loadExample(ui.example.value);
  history.replaceState(null, "", "#example=" + encodeURIComponent(ui.example.value));
  current = null; renderResult(); ui.summary.textContent = "";
};

async function init() {
  examples = await (await fetch("examples.json")).json();
  ui.example.replaceChildren(h("option", { value: "" }, "Example: (edited)"));
  let group = null;
  for (const ex of examples) {
    if (!group || group.label !== ex.group) ui.example.append(group = h("optgroup", { label: ex.group }));
    group.append(h("option", { value: ex.id }, `Example: ${ex.title}`));
  }
  const want = await readFragment(location.hash);
  if (want.code !== undefined) { setProgram(editor, want.code); ui.example.value = ""; }
  else loadExample(want.example);
  clear(editor);
}
init();
window.addEventListener("hashchange", async () => {
  const want = await readFragment(location.hash);
  if (want.code !== undefined) setProgram(editor, want.code);
  else if (want.example) loadExample(want.example);
});
