// The playground's editor: CodeMirror 6 with a minimal setup (docs/design/website.md 4.6), Hugin
// highlighting from the VS Code grammar, the compiler's diagnostics inline (underline, a line below the
// code with the fix suggestions as buttons, and the lint tooltip and keyboard actions), and, after a
// check, a run or a pause in typing, the compiler's semantic highlighting (main.js asks for it). An edit
// clears the diagnostics. Lines do not wrap, as in the landing page's code card: long lines scroll
// horizontally, and the inline diagnostics are as wide as the visible editor (play.css).
import { EditorView, keymap, lineNumbers, drawSelection, Decoration, WidgetType } from "@codemirror/view";
import { EditorState, StateField, StateEffect, Compartment } from "@codemirror/state";
import { history, defaultKeymap, historyKeymap, indentWithTab } from "@codemirror/commands";
import { bracketMatching } from "@codemirror/language";
import { setDiagnostics, lintKeymap } from "@codemirror/lint";
import { huginLanguage, huginHighlight } from "./hugin-lang.js";

const SEVERITY = { error: "error", warning: "warning" };

// 1-based line and column (UTF-16 units, as the compiler's strings) -> document offset
export function offset(doc, pos) {
  const line = doc.line(Math.min(Math.max(pos.line, 1), doc.lines));
  return Math.min(line.from + Math.max(pos.col - 1, 0), line.to);
}

// the span of a diagnostic in the program (not in a std/ module), the primary one first
export function mainSpan(d) {
  const spans = (d.spans || []).filter((s) => !/^std\//.test(s.file || ""));
  return spans.find((s) => s.primary) || spans[0] || null;
}

export function applySuggestion(view, s) {
  const changes = s.edits.map((e) => ({
    from: offset(view.state.doc, e.span.start),
    to: offset(view.state.doc, e.span.end),
    insert: e.replacement,
  }));
  view.dispatch({ changes, userEvent: "input.fix" });
  view.focus();
}

class InlineDiagnostic extends WidgetType {
  constructor(d) { super(); this.d = d; }
  eq(other) { return other.d === this.d; }
  toDOM(view) {
    const d = this.d, el = document.createElement("div");
    el.className = "inline-diag " + (d.level === "error" ? "error" : "warning");
    const code = d.code && d.code.id ? `[${d.code.id}]` : "";
    el.append(`${d.level}${code}: ${d.message}`);
    if (d.code && d.code.url) {
      const a = document.createElement("a");
      a.href = d.code.url; a.textContent = d.code.id; a.target = "_blank"; a.rel = "noopener";
      el.append(" · ", a);
    }
    for (const s of d.suggestions || []) {
      const b = document.createElement("button");
      b.type = "button"; b.className = "fix"; b.textContent = s.message;
      b.onclick = () => applySuggestion(view, s);
      el.append(" · ", b);
    }
    return el;
  }
  ignoreEvent() { return true; }
}

const setInline = StateEffect.define();
const setTokens = StateEffect.define();

// decorations set by an effect; an edit drops them, or (`keep`) maps them through the change
function decorationField(effect, keep = false) {
  return StateField.define({
    create: () => Decoration.none,
    update(deco, tr) {
      for (const e of tr.effects) if (e.is(effect)) return e.value;
      return !tr.docChanged ? deco : keep ? deco.map(tr.changes) : Decoration.none;
    },
    provide: (f) => EditorView.decorations.from(f),
  });
}
const inlineField = decorationField(setInline);
// the semantic tokens survive edits (moved with the text) until the next highlighting replaces them
const tokenField = decorationField(setTokens, true);
const lexical = new Compartment();

export function createEditor(parent, doc, { onRun, onEdit }) {
  const view = new EditorView({
    parent,
    state: EditorState.create({
      doc,
      extensions: [
        lineNumbers(),
        history(),
        drawSelection(),
        bracketMatching(),
        huginLanguage,
        lexical.of(huginHighlight),
        inlineField,
        tokenField,
        EditorView.contentAttributes.of({ class: "hugin", "aria-label": "Program", spellcheck: "false" }),
        keymap.of([
          { key: "Mod-Enter", run: () => (onRun(), true) },
          indentWithTab,
          ...defaultKeymap,
          ...historyKeymap,
          ...lintKeymap,
        ]),
        EditorView.updateListener.of((u) => {
          if (u.docChanged) {
            if (u.view.compilerSaid) queueMicrotask(() => clearDiagnostics(u.view));
            onEdit();
          }
        }),
      ],
    }),
  });
  return view;
}

// the compiler's diagnostics, shown in the editor
export function showDiagnostics(view, diagnostics) {
  const doc = view.state.doc, lint = [], widgets = [];
  for (const d of diagnostics) {
    const span = mainSpan(d);
    if (!span) continue;
    const from = offset(doc, span.start), to = Math.max(offset(doc, span.end), from);
    lint.push({
      from, to,
      severity: SEVERITY[d.level] || "info",
      source: d.code && d.code.id,
      message: d.message,
      actions: (d.suggestions || []).map((s) => ({ name: s.message, apply: (v) => applySuggestion(v, s) })),
    });
    const line = doc.lineAt(to);
    widgets.push(Decoration.widget({ widget: new InlineDiagnostic(d), block: true, side: 1 }).range(line.to));
  }
  view.compilerSaid = true;
  view.dispatch(setDiagnostics(view.state, lint));
  view.dispatch({ effects: setInline.of(Decoration.set(widgets, true)) });
}

// the compiler's semantic tokens (runs of text and classes, as `hugin highlight`), replacing the
// grammar's lexical highlighting; they stay, moved with the text, until the next highlighting
export function showTokens(view, runs) {
  if (!runs || runs.map((r) => r[0]).join("") !== view.state.doc.toString()) return;
  const marks = [];
  let at = 0;
  for (const [text, classes] of runs) {
    if (classes && classes.length && text.length)
      marks.push(Decoration.mark({ class: classes.map((c) => "hg-" + c).join(" ") }).range(at, at + text.length));
    at += text.length;
  }
  view.dispatch({ effects: [setTokens.of(Decoration.set(marks, true)), lexical.reconfigure([])] });
}

// what the compiler said about the text that an edit makes stale: the diagnostics
function clearDiagnostics(view) {
  view.compilerSaid = false;
  view.dispatch(setDiagnostics(view.state, []));
  view.dispatch({ effects: setInline.of(Decoration.none) });
}

export function clear(view) {
  view.compilerSaid = false;
  view.dispatch(setDiagnostics(view.state, []));
  view.dispatch({
    effects: [setInline.of(Decoration.none), setTokens.of(Decoration.none), lexical.reconfigure(huginHighlight)],
  });
}

// a new program: the grammar's highlighting until the compiler's arrives
export function setProgram(view, text) {
  view.dispatch({ changes: { from: 0, to: view.state.doc.length, insert: text } });
  clear(view);
}
