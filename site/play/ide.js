// The playground's editor features from the annotation table (issue #147, docs/design/web-ide.md 4.3, 6):
// hover, the info bar, Ctrl-K Ctrl-I, go to definition (F12, Ctrl/Cmd-click), the occurrences of the name
// at the cursor and the references panel (Shift-F12). The worker sends the table with every analysis,
// check and run (`info`: names with their hover, occurrence group and declaration, in UTF-16 offsets, as
// CodeMirror's positions); everything here is answered on the main thread from it, with no request.
//
// The table's names are a RangeSet mapped through every edit, as the semantic tokens are; a name that an
// edit touches is dropped, so hovering untouched code keeps working while the reader types, until the next
// analysis replaces the table.
import { StateField, StateEffect, RangeSet, RangeValue, ChangeSet, MapMode } from "@codemirror/state";
import { EditorView, Decoration, hoverTooltip, showTooltip, showPanel, keymap } from "@codemirror/view";
import { StringStream } from "@codemirror/language";
import { parser } from "./hugin-lang.js";

// where a declaration of the bundled standard library is documented: its module's page in the reference
const REFERENCE = "../reference/";

class Name extends RangeValue {
  constructor(data) { super(); this.data = data; }
  eq(other) { return other === this; }
}

const setInfo = StateEffect.define();
const empty = { names: RangeSet.empty, changes: ChangeSet.empty(0) };

// info: { names: [[from, to, hover, group, flags, target?]], hovers: [[signature, note, …]] } (worker.js)
function table(info, length) {
  if (!info || !info.names) return { ...empty, changes: ChangeSet.empty(length) };
  const hovers = (info.hovers || []).map(([signature, ...notes]) => ({ signature, notes }));
  const values = info.names.map(([from, to, hover, group, flags]) =>
    new Name({ hover: hover == null ? null : hovers[hover], group, decl: (flags & 1) !== 0, target: null }));
  const byStart = new Map();
  info.names.forEach((n, i) => { if (values[i].data.decl) byStart.set(n[0], values[i]); });
  info.names.forEach((n, i) => {
    const t = n[5];
    if (Array.isArray(t)) values[i].data.target = { module: t[0], name: t[1] };
    else if (typeof t === "number") values[i].data.target = byStart.has(t) ? { ref: byStart.get(t) } : { pos: t };
  });
  const ranges = [];
  info.names.forEach((n, i) => { if (n[1] > n[0] && n[1] <= length) ranges.push(values[i].range(n[0], n[1])); });
  return { names: RangeSet.of(ranges, true), changes: ChangeSet.empty(length) };
}

const tableField = StateField.define({
  create: () => empty,
  update(value, tr) {
    for (const e of tr.effects) if (e.is(setInfo)) return table(e.value, tr.newDoc.length);
    if (!tr.docChanged) return value;
    const touched = [];
    tr.changes.iterChangedRanges((fromA, toA) => touched.push([fromA, toA]));
    const names = value.names
      .update({ filter: (from, to) => !touched.some(([a, b]) => from <= b && a <= to) })
      .map(tr.changes);
    return { names, changes: value.changes.compose(tr.changes) };
  },
});

// the name at a position: the one around it, else the one ending there (the cursor right after a name)
export function nameAt(state, pos) {
  let found = null;
  state.field(tableField).names.between(pos, pos, (from, to, value) => {
    if (from <= pos && pos < to) { found = { from, to, value }; return false; }
    if (to === pos && !found) found = { from, to, value };
  });
  return found;
}

function rangeOf(state, value) {
  for (const it = state.field(tableField).names.iter(); it.value; it.next())
    if (it.value === value) return { from: it.from, to: it.to };
  return null;
}

function occurrences(state, group) {
  const out = [];
  for (const it = state.field(tableField).names.iter(); it.value; it.next())
    if (it.value.data.group === group) out.push({ from: it.from, to: it.to, value: it.value });
  return out;
}

// where the declaration of a name is now: a range in the program, a library declaration, or nothing
function declaration(state, value) {
  const t = value.data.target;
  if (!t) return null;
  if (t.module) return { library: t };
  if (t.ref) return rangeOf(state, t.ref);
  const at = state.field(tableField).changes.mapPos(t.pos, 1, MapMode.TrackDel);
  return at == null ? null : { from: at, to: at };
}

// --- rendering of hovers ---------------------------------------------------------------------------
const el = (tag, cls, ...children) => {
  const e = document.createElement(tag);
  if (cls) e.className = cls;
  e.append(...children);
  return e;
};

// Hugin code with the classes of the playground's grammar (hugin-lang.js)
function code(text, block) {
  const out = el(block ? "pre" : "code", "hugin" + (block ? " hg-code" : ""));
  text.split("\n").forEach((line, i) => {
    if (i) out.append("\n");
    const stream = new StringStream(line, 2, 2), state = parser.startState();
    while (!stream.eol()) {
      const start = stream.pos, style = parser.token(stream, state);
      if (stream.pos <= start) stream.pos = start + 1;
      const piece = line.slice(start, stream.pos);
      out.append(style ? el("span", "hg-" + style, piece) : piece);
    }
  });
  return out;
}

// a note of the compiler: text in which `…` is code, **…** strong, a fenced ```hugin block code, and two
// spaces before a line break a line break (the language server's Markdown, without a Markdown library)
function note(text) {
  const out = el("div", "hg-note");
  text.split(/```hugin\n([\s\S]*?)\n```/).forEach((part, i) => {
    if (i % 2) return out.append(code(part, true));
    const lines = part.replace(/^\n+|\n+$/g, "").split(/ {2}\n|\n/);
    lines.forEach((line, j) => {
      if (j) out.append(el("br"));
      line.split(/(`[^`]*`|\*\*[^*]+\*\*)/).forEach((s) => {
        if (/^`[^`]*`$/.test(s)) out.append(el("code", null, s.slice(1, -1)));
        else if (/^\*\*[^*]+\*\*$/.test(s)) out.append(el("strong", null, s.slice(2, -2)));
        else if (s) out.append(s);
      });
    });
  });
  return out;
}

function hoverDom(hover) {
  const dom = el("div", "hg-hover");
  if (hover.signature) dom.append(el("div", "hg-signature", code(hover.signature)));
  for (const n of hover.notes) dom.append(note(n));
  return dom;
}

function plainText(hover) {
  return [hover.signature, ...hover.notes].filter(Boolean).join(". ").replace(/```hugin\n|\n```|\*\*|`/g, "").replace(/\s+/g, " ");
}

// --- hover: the mouse, and Ctrl-K Ctrl-I at the cursor ----------------------------------------------
const mouseHover = hoverTooltip((view, pos) => {
  const n = nameAt(view.state, pos);
  if (!n || !n.value.data.hover) return null;
  return { pos: n.from, end: n.to, above: true, create: () => ({ dom: hoverDom(n.value.data.hover) }) };
}, { hoverTime: 300 });

const toggleTip = StateEffect.define();
const cursorTip = StateField.define({
  create: () => null,
  update(tip, tr) {
    for (const e of tr.effects) if (e.is(toggleTip)) return e.value;
    return tr.docChanged || tr.selection ? null : tip;
  },
  provide: (f) => showTooltip.from(f),
});

function tipAtCursor(view) {
  const n = nameAt(view.state, view.state.selection.main.head);
  if (!n || !n.value.data.hover) {
    announce(view, "No information at the cursor");
    return true;
  }
  const hover = n.value.data.hover;
  view.dispatch({ effects: toggleTip.of({ pos: n.from, end: n.to, above: true, create: () => ({ dom: hoverDom(hover) }) }) });
  announce(view, plainText(hover));
  return true;
}

function closeTip(view) {
  if (!view.state.field(cursorTip)) return false;
  view.dispatch({ effects: toggleTip.of(null) });
  return true;
}

// a polite live region in the info bar: what Ctrl-K Ctrl-I opened, for screen readers
function announce(view, text) {
  const live = view.dom.querySelector(".hg-live");
  if (!live) return;
  live.textContent = "";
  setTimeout(() => { live.textContent = text; }, 50);
}

// --- go to definition -------------------------------------------------------------------------------
function goTo(view, n) {
  if (!n) return false;
  const d = declaration(view.state, n.value);
  if (!d) return false;
  if (d.library) {
    window.open(REFERENCE + d.library.module + ".html", "_blank", "noopener");
    return true;
  }
  view.dispatch({ selection: { anchor: d.from, head: d.to }, effects: EditorView.scrollIntoView(d.from, { y: "center" }) });
  view.focus();
  return true;
}

const definitionAtCursor = (view) => goTo(view, nameAt(view.state, view.state.selection.main.head)) || true;

const modClick = EditorView.domEventHandlers({
  mousedown(e, view) {
    if (!(e.ctrlKey || e.metaKey) || e.button !== 0) return false;
    const pos = view.posAtCoords({ x: e.clientX, y: e.clientY });
    if (pos == null) return false;
    const n = nameAt(view.state, pos);
    if (!n || !n.value.data.target) return false;
    e.preventDefault();
    return goTo(view, n);
  },
});

// --- occurrences of the name at the cursor ----------------------------------------------------------
const occurrenceMark = Decoration.mark({ class: "hg-occurrence" });
const occurrenceMarks = EditorView.decorations.compute(["selection", tableField], (state) => {
  const n = nameAt(state, state.selection.main.head);
  if (!n) return Decoration.none;
  return Decoration.set(occurrences(state, n.value.data.group).map((o) => occurrenceMark.range(o.from, o.to)));
});

// --- the references panel (Shift-F12) ---------------------------------------------------------------
const setReferences = StateEffect.define();
const referencesField = StateField.define({
  create: () => null,
  update(v, tr) {
    for (const e of tr.effects) if (e.is(setReferences)) return e.value;
    return tr.docChanged ? null : v;
  },
  provide: (f) => showPanel.from(f, (v) => (v ? (view) => referencesPanel(view, v) : null)),
});

function referencesPanel(view, { name, list }) {
  const dom = el("div", "hg-references");
  dom.setAttribute("role", "region");
  dom.setAttribute("aria-label", `References to ${name}`);
  const close = el("button", "hg-close", "×");
  close.type = "button";
  close.title = "Close (Escape)";
  close.setAttribute("aria-label", "Close the references");
  close.onclick = () => closeReferences(view);
  dom.append(el("div", "hg-references-head", el("span", null, `${list.length} ${list.length === 1 ? "occurrence" : "occurrences"} of `, el("code", null, name)), close));
  const items = el("ul", "hg-references-list");
  for (const o of list) {
    const line = view.state.doc.lineAt(o.from);
    const b = el("button", null, el("span", "hg-line", `${line.number}`), " ", line.text.trim());
    b.type = "button";
    b.onclick = () => {
      view.dispatch({ selection: { anchor: o.from, head: o.to }, effects: EditorView.scrollIntoView(o.from, { y: "center" }) });
      view.focus();
    };
    items.append(el("li", null, b));
  }
  dom.append(items);
  dom.addEventListener("keydown", (e) => {
    const buttons = [...items.querySelectorAll("button")];
    const i = buttons.indexOf(document.activeElement);
    if (e.key === "Escape") { e.preventDefault(); closeReferences(view); }
    else if (e.key === "ArrowDown" && i >= 0) { e.preventDefault(); buttons[Math.min(i + 1, buttons.length - 1)].focus(); }
    else if (e.key === "ArrowUp" && i >= 0) { e.preventDefault(); buttons[Math.max(i - 1, 0)].focus(); }
  });
  return { dom, top: false, mount: () => items.querySelector("button")?.focus() };
}

function referencesAtCursor(view) {
  const n = nameAt(view.state, view.state.selection.main.head);
  if (!n) return true;
  const name = view.state.sliceDoc(n.from, n.to);
  view.dispatch({ effects: setReferences.of({ name, list: occurrences(view.state, n.value.data.group) }) });
  return true;
}

function closeReferences(view) {
  if (!view.state.field(referencesField)) return false;
  view.dispatch({ effects: setReferences.of(null) });
  view.focus();
  return true;
}

// --- the info bar: what is at the cursor --------------------------------------------------------------
function infoBar(view) {
  const dom = el("div", "hg-infobar");
  const text = el("span", "hg-infobar-text");
  const button = el("button", "fix", "Definition");
  button.type = "button";
  button.onclick = () => definitionAtCursor(view);
  const live = el("div", "hg-live");
  live.setAttribute("aria-live", "polite");
  dom.append(text, button, live);
  const render = (state) => {
    const n = nameAt(state, state.selection.main.head);
    const hover = n && n.value.data.hover;
    text.replaceChildren();
    if (hover) text.append(hover.signature ? code(hover.signature) : note(hover.notes[0].split("\n")[0]));
    button.hidden = !(n && declaration(state, n.value));
  };
  render(view.state);
  return {
    dom,
    update(u) {
      if (u.selectionSet || u.docChanged || u.transactions.some((t) => t.effects.some((e) => e.is(setInfo)))) render(u.state);
    },
  };
}

// --- the extension and the page's entry points -------------------------------------------------------
export function ideExtensions() {
  return [
    tableField,
    mouseHover,
    cursorTip,
    modClick,
    occurrenceMarks,
    referencesField,
    showPanel.of(infoBar),
    keymap.of([
      { key: "F12", run: definitionAtCursor },
      { key: "Shift-F12", run: referencesAtCursor },
      { key: "Mod-k Mod-i", run: tipAtCursor },
      { key: "Escape", run: (view) => closeTip(view) || closeReferences(view) },
    ]),
  ];
}

// the annotation table of the editor's current text (null: none, e.g. a new program)
export function showInfo(view, info) {
  view.dispatch({ effects: setInfo.of(info || null) });
}
