// Inlay hints in the playground (issue #147, docs/design/web-ide.md 6.1, batch P4): what the compiler
// inserted and inferred, shown inline as the language server's inlay hints are: the quotes, splices and
// lifts of stage inference (`staging`), inferred implicit arguments (`implicit`) and universe levels
// (`level`). They come with the annotation table (`info.hints`: [at, label, tooltip, kind], UTF-16
// offsets), are off by default, and are switched in the toolbar; the choice is kept in localStorage.
import { StateField, StateEffect, Compartment } from "@codemirror/state";
import { EditorView, Decoration, WidgetType } from "@codemirror/view";

const KEY = "hugin-play-hints";

class Hint extends WidgetType {
  constructor(label, tooltip, kind) { super(); this.label = label; this.tooltip = tooltip; this.kind = kind; }
  eq(o) { return o.label === this.label && o.tooltip === this.tooltip && o.kind === this.kind; }
  toDOM() {
    const el = document.createElement("span");
    el.className = "hg-hint hg-hint-" + this.kind;
    el.textContent = this.label;
    if (this.tooltip) el.title = this.tooltip;
    el.setAttribute("aria-hidden", "true");
    return el;
  }
  ignoreEvent() { return false; }
}

const setHints = StateEffect.define();
// the hints, moved with the text until the next analysis replaces them
const hintsField = StateField.define({
  create: () => Decoration.none,
  update(deco, tr) {
    for (const e of tr.effects) if (e.is(setHints)) return e.value;
    return tr.docChanged ? deco.map(tr.changes) : deco;
  },
});

const shown = new Compartment();
const visible = EditorView.decorations.from(hintsField);

export function savedChoice() {
  try {
    return localStorage.getItem(KEY) === "on";
  } catch (_) {
    return false;
  }
}

export function hintsExtension(on = savedChoice()) {
  return [hintsField, shown.of(on ? visible : [])];
}

// the hints of the table (null: none)
export function showHints(view, hints) {
  const length = view.state.doc.length;
  const widgets = (hints || [])
    .filter(([at]) => at >= 0 && at <= length)
    .map(([at, label, tooltip, kind]) => Decoration.widget({ widget: new Hint(label, tooltip, kind), side: kind === "implicit" ? 1 : -1 }).range(at));
  view.dispatch({ effects: setHints.of(Decoration.set(widgets, true)) });
}

export function setHintsShown(view, on) {
  try {
    localStorage.setItem(KEY, on ? "on" : "off");
  } catch (_) {
    // the choice holds for this page only
  }
  view.dispatch({ effects: shown.reconfigure(on ? visible : []) });
}
