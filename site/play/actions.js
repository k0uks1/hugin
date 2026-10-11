// Code actions at the cursor in the playground (issue #147, docs/design/web-ide.md 6.1 and 9, batch P3):
// Ctrl-. opens a menu of what the compiler offers at the cursor (hugin.ide.Fixes: split a pattern
// variable, add the missing clauses, add a clause, refine a hole, and the diagnostics' suggestions), asked
// from the worker (`actions`). When the cursor rests, the same request tells the info bar (ide.js)
// whether to show its "Fix" button, the touch path to the menu. The diagnostics' own lint actions and
// inline buttons stay as they are (editor.js).
import { StateField, StateEffect } from "@codemirror/state";
import { ViewPlugin, showTooltip, keymap } from "@codemirror/view";

const REST_MS = 250;

// the actions known for the cursor: { pos, list } (list: the worker's actions), or null
const setFixes = StateEffect.define();
export const fixesField = StateField.define({
  create: () => null,
  update(v, tr) {
    for (const e of tr.effects) if (e.is(setFixes)) return e.value;
    return tr.docChanged || tr.selection ? null : v;
  },
});

export const hasFixes = (state) => !!state.field(fixesField, false)?.list.length;

// the menu: a tooltip at the cursor with one button per action
const setMenu = StateEffect.define();
const menuField = StateField.define({
  create: () => null,
  update(v, tr) {
    for (const e of tr.effects) if (e.is(setMenu)) return e.value;
    return tr.docChanged || tr.selection ? null : v;
  },
  provide: (f) => showTooltip.from(f, (m) => m && m.tooltip),
});

function apply(view, action) {
  const changes = action.edits
    .map((e) => ({ from: e.from, to: e.to, insert: e.insert }))
    .filter((c) => c.from <= c.to && c.to <= view.state.doc.length);
  view.dispatch({ changes, effects: setMenu.of(null), userEvent: "input.fix", scrollIntoView: true });
  view.focus();
}

function closeMenu(view) {
  if (!view.state.field(menuField)) return false;
  view.dispatch({ effects: setMenu.of(null) });
  view.focus();
  return true;
}

function menuDom(view, list) {
  const dom = document.createElement("div");
  dom.className = "hg-actions";
  const menu = document.createElement("ul");
  menu.setAttribute("role", "menu");
  menu.setAttribute("aria-label", "Actions at the cursor");
  if (!list.length) {
    const li = document.createElement("li");
    li.className = "hg-actions-none";
    li.textContent = "No actions at the cursor";
    menu.append(li);
  }
  for (const a of list) {
    const b = document.createElement("button");
    b.type = "button";
    b.setAttribute("role", "menuitem");
    b.textContent = a.title;
    if (a.preferred) b.classList.add("preferred");
    b.onclick = () => apply(view, a);
    const li = document.createElement("li");
    li.append(b);
    menu.append(li);
  }
  dom.append(menu);
  dom.addEventListener("keydown", (e) => {
    const items = [...menu.querySelectorAll("button")];
    const i = items.indexOf(document.activeElement);
    if (e.key === "Escape") { e.preventDefault(); closeMenu(view); }
    else if (e.key === "ArrowDown") { e.preventDefault(); items[(i + 1) % items.length]?.focus(); }
    else if (e.key === "ArrowUp") { e.preventDefault(); items[(i - 1 + items.length) % items.length]?.focus(); }
    else if (e.key === "Home") { e.preventDefault(); items[0]?.focus(); }
    else if (e.key === "End") { e.preventDefault(); items.at(-1)?.focus(); }
    else if (e.key === "Tab") { e.preventDefault(); closeMenu(view); }
  });
  return dom;
}

// `ask(source, from, to)` resolves to the worker's { version, actions } or to null (busy, unavailable or
// stale); the extension and the function that opens the menu (Ctrl-., the info bar's "Fix" button)
export function actionsExtension(ask) {
  async function fixesAt(view) {
    const sel = view.state.selection.main;
    const known = view.state.field(fixesField);
    if (known && known.pos === sel.head) return known.list;
    const doc = view.state.doc;
    const answer = await ask(doc.toString(), sel.from, sel.to);
    if (!answer || view.state.doc !== doc || view.state.selection.main.head !== sel.head) return null;
    view.dispatch({ effects: setFixes.of({ pos: sel.head, list: answer.actions }) });
    return answer.actions;
  }

  async function openMenu(view) {
    const pos = view.state.selection.main.head;
    const list = await fixesAt(view);
    if (list == null) return;
    view.dispatch({
      effects: setMenu.of({ tooltip: { pos, above: false, create: (v) => {
        const dom = menuDom(v, list);
        return { dom, mount: () => (dom.querySelector("button") || dom).focus?.() };
      } } }),
    });
  }

  // when the cursor rests, ask what is offered there (for the info bar's "Fix" button)
  const rest = ViewPlugin.fromClass(class {
    constructor(view) { this.view = view; this.timer = null; this.schedule(); }
    update(u) { if (u.docChanged || u.selectionSet) this.schedule(); }
    schedule() {
      clearTimeout(this.timer);
      this.timer = setTimeout(() => fixesAt(this.view).catch(() => {}), REST_MS);
    }
    destroy() { clearTimeout(this.timer); }
  });

  const extension = [
    fixesField,
    menuField,
    rest,
    keymap.of([
      { key: "Mod-.", run: (view) => (openMenu(view), true) },
      { key: "Escape", run: closeMenu },
    ]),
  ];
  return { extension, openMenu };
}
