// Hovers and definitions in the Hugin code blocks of the reference (issue #132, docs/design/web-ide.md,
// sections 7 and 9). highlight.py renders a block as <code class="hugin" data-hg tabindex="0"> and each
// name in it as <span data-i> or <a data-i href tabindex="-1">; data-i indexes the page's hover texts,
// the JSON array in <script type="application/json" id="hg-hovers"> after the page's blocks. A hover is
// [signature or null, note, ...]; in a note, `...` becomes <code> and a line break a new line. The
// texts are inserted as text, never as HTML. One popup (role="tooltip") serves the page:
// - mouse: it opens after 300 ms over a name and stays while the pointer is over the name or the popup;
// - keyboard: a block is one tab stop; ArrowRight/ArrowLeft, Home/End move to a name and show its popup,
//   Enter follows the name's link, Escape hides the popup and returns to the block, Tab leaves it;
// - touch: the first tap on a name shows its popup (with a "Definition" link) instead of following the
//   link; a tap on the same name or outside closes it. Scrolling a block fires no click.
(() => {
  "use strict";
  const tables = new Map(); // block -> its page's hover texts (print.html holds the tables of every page)
  let pending = [];
  for (const el of document.querySelectorAll("code[data-hg], script#hg-hovers")) {
    if (el.tagName === "CODE") {
      pending.push(el);
      continue;
    }
    let table = [];
    try {
      table = JSON.parse(el.textContent);
    } catch (e) {}
    for (const block of pending) tables.set(block, table);
    pending = [];
  }
  if (!tables.size) return;

  const NAME = "[data-i],a[href]";
  const popup = document.createElement("div");
  popup.id = "hg-popup";
  popup.className = "hg-popup";
  popup.setAttribute("role", "tooltip");
  popup.hidden = true;
  document.body.append(popup);
  const noHover = matchMedia("(hover: none)");
  let current = null; // the name whose popup is shown
  let byKey = false; // shown from the keyboard: the mouse does not close it
  let pointer = "mouse";
  let showTimer = 0;
  let hideTimer = 0;

  const blockOf = (el) => el && el.closest && el.closest("code[data-hg]");
  const nameIn = (el) => {
    const name = el && el.closest && el.closest(NAME);
    return name && tables.has(blockOf(name)) ? name : null;
  };
  const namesOf = (block) => Array.from(block.querySelectorAll(NAME));

  // the occurrences of a name in its block: the names that link where it links, and that declaration
  function occurrences(el) {
    const key = el.getAttribute("href") || (el.id && "#" + el.id);
    if (!key) return [el];
    return namesOf(blockOf(el)).filter((n) => n.getAttribute("href") === key || "#" + n.id === key);
  }

  function element(tag, cls, text) {
    const e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text != null) e.textContent = text;
    return e;
  }

  function fill(el) {
    popup.replaceChildren();
    const hover = el.hasAttribute("data-i") ? tables.get(blockOf(el))[+el.getAttribute("data-i")] : null;
    if (hover) {
      if (hover[0] != null) {
        const sig = element("div", "hg-sig");
        sig.append(element("code", "", hover[0]));
        popup.append(sig);
      }
      for (const note of hover.slice(1)) {
        // a note may hold several lines (Markdown line breaks, as the language server sends them)
        for (const text of note.split(/ *\n/)) {
          const line = element("div", "hg-note");
          text.split("`").forEach((part, k) => line.append(k % 2 ? element("code", "", part) : part));
          popup.append(line);
        }
      }
    }
    const href = el.getAttribute("href");
    if (href) {
      const link = element("a", "hg-def", "Definition");
      link.href = href;
      popup.append(link);
    }
  }

  // under the name, or over it if there is no room below; inside the viewport horizontally
  function place(el) {
    const r = el.getBoundingClientRect();
    const width = document.documentElement.clientWidth;
    popup.style.left = popup.style.top = "0px";
    const w = popup.offsetWidth;
    const h = popup.offsetHeight;
    const x = Math.max(8, Math.min(r.left, width - w - 8));
    let y = r.bottom + 4;
    if (y + h > innerHeight && r.top - 4 - h >= 0) y = r.top - 4 - h;
    popup.style.left = x + scrollX + "px";
    popup.style.top = y + scrollY + "px";
  }

  function show(el, key) {
    clearTimeout(showTimer);
    clearTimeout(hideTimer);
    byKey = key;
    if (current === el) return;
    hide();
    fill(el);
    if (!popup.firstChild) return;
    current = el;
    popup.hidden = false;
    place(el);
    el.setAttribute("aria-describedby", popup.id);
    for (const n of occurrences(el)) n.classList.add("hg-occ");
  }

  function hide() {
    clearTimeout(showTimer);
    clearTimeout(hideTimer);
    if (!current) return;
    for (const n of occurrences(current)) n.classList.remove("hg-occ");
    current.removeAttribute("aria-describedby");
    popup.hidden = true;
    current = null;
  }

  // the last pointer that pressed or moved: after a tap, Chromium sends mouse pointerover events where
  // the page moves under the finger, which must not open or close popups
  for (const type of ["pointerdown", "pointermove"]) document.addEventListener(type, (e) => (pointer = e.pointerType), true);

  // mouse
  document.addEventListener("pointerover", (e) => {
    if (e.pointerType !== "mouse" || pointer !== "mouse") return;
    clearTimeout(showTimer);
    if (popup.contains(e.target)) return clearTimeout(hideTimer);
    const el = nameIn(e.target);
    if (el) {
      if (el === current) return clearTimeout(hideTimer);
      showTimer = setTimeout(() => show(el, false), 300);
    }
    if (current && !byKey && el !== current) {
      clearTimeout(hideTimer);
      hideTimer = setTimeout(hide, 300);
    }
  });

  // touch: the first tap shows the popup, a second tap on the name or a tap outside closes it
  document.addEventListener("click", (e) => {
    if (popup.contains(e.target)) {
      if (e.target.closest("a")) setTimeout(hide); // the Definition link, followed by the browser
      return;
    }
    const el = nameIn(e.target);
    if (!el || !(pointer === "touch" || pointer === "pen" || noHover.matches)) return hide();
    e.preventDefault();
    if (el === current) hide();
    else show(el, false);
  });

  // keyboard: roving focus over the names of a block
  let focused = null;
  function focus(block, el) {
    if (focused && focused !== el) focused.tabIndex = -1;
    focused = el;
    el.tabIndex = 0;
    block.tabIndex = -1;
    el.focus({ preventScroll: true });
    el.scrollIntoView({ block: "nearest", inline: "nearest", behavior: "instant" });
    show(el, true);
  }
  function leave(block) {
    if (focused) focused.tabIndex = -1;
    focused = null;
    block.tabIndex = 0;
  }

  function onKey(e) {
    if (e.altKey || e.ctrlKey || e.metaKey || e.shiftKey) return;
    const block = e.currentTarget;
    const names = namesOf(block);
    const at = names.indexOf(document.activeElement);
    let next = null;
    if (e.key === "ArrowRight") next = names[at < 0 ? 0 : Math.min(at + 1, names.length - 1)];
    else if (e.key === "ArrowLeft") next = names[at < 0 ? names.length - 1 : Math.max(at - 1, 0)];
    else if (e.key === "Home") next = names[0];
    else if (e.key === "End") next = names[names.length - 1];
    else if (e.key === "Escape") {
      hide();
      leave(block);
      block.focus();
    } else if (e.key === "Enter" && at >= 0) {
      // a declaration in the same block: move there; other links are followed by the browser
      const href = names[at].getAttribute("href") || "";
      const target = href.startsWith("#") && document.getElementById(href.slice(1));
      if (!target || !block.contains(target)) return;
      next = target;
    } else return;
    e.preventDefault();
    e.stopPropagation(); // mdBook's ArrowLeft/ArrowRight turn the page
    if (next) focus(block, next);
  }

  for (const block of tables.keys()) {
    block.addEventListener("keydown", onKey);
    block.addEventListener("focusout", (e) => {
      if (block.contains(e.relatedTarget)) return;
      leave(block);
      if (byKey) hide();
    });
  }
  document.addEventListener("keydown", (e) => e.key === "Escape" && hide());
  addEventListener("resize", hide);
})();
