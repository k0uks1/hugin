// Hugin highlighting for CodeMirror, derived from the VS Code grammar
// (editors/vscode/syntaxes/hugin.tmLanguage.json, bundled at build time): one grammar, two editors.
// The grammar's subset (match, begin/end with nesting, include, captures, lookbehind) runs as a
// StreamLanguage whose state is the stack of open begin/end rules. Scopes become the classes of
// `hugin highlight` (hg-*), so the colours are those of the landing page and the reference.
import { StreamLanguage, HighlightStyle, syntaxHighlighting } from "@codemirror/language";
import { Tag } from "@lezer/highlight";
import grammar from "../../editors/vscode/syntaxes/hugin.tmLanguage.json";

// TextMate scope prefix -> hg-* class (the first matching prefix wins); unlisted scopes are plain text,
// as in the compiler's lexical classes (`=`, `:`, `.` are not coloured)
const SCOPES = [
  ["comment", "comment"], ["punctuation.definition.comment", "comment"],
  ["string", "string"], ["punctuation.definition.string", "string"],
  ["constant.character.escape", "string"], ["invalid.illegal.escape", "string"],
  ["constant.numeric", "number"],
  ["keyword.control.directive", "decorator"],
  ["entity.name.label", "label"], ["keyword.other.hole", "label"],
  ["entity.name.function.declaration", "declaration"],
  ["storage.type", "keyword"], ["keyword.other.where", "keyword"], ["keyword.operator.word", "keyword"],
  ["support.function.aggregate", "keyword"], ["support.type.base", "type"],
  ["punctuation.section.quote", "keyword"],
  ["keyword.operator.splice", "operator"], ["keyword.operator.lift", "operator"],
  ["keyword.operator.cons", "operator"], ["keyword.operator.rule", "operator"],
  ["keyword.operator.type", "operator"],
  ["variable", "variable"],
];
const CLASSES = ["comment", "string", "number", "decorator", "label", "declaration", "keyword", "type", "operator", "variable"];

function styleOf(scope) {
  if (!scope) return null;
  for (const [prefix, cls] of SCOPES) if (scope === prefix || scope.startsWith(prefix + ".")) return cls;
  return null;
}

// compile the grammar: every regex sticky (matched at the stream position on the whole line, so that
// lookbehind sees the text before it), includes resolved lazily
const compiled = new Map();
function compileRule(rule) {
  if (compiled.has(rule)) return compiled.get(rule);
  const out = { name: rule.name, captures: rule.captures };
  compiled.set(rule, out);
  if (rule.include) out.include = rule.include;
  if (rule.match) out.match = new RegExp(rule.match, "duy");
  if (rule.begin) {
    out.begin = new RegExp(rule.begin, "duy");
    out.end = new RegExp(rule.end, "duy");
    out.beginCaptures = rule.beginCaptures;
    out.endCaptures = rule.endCaptures;
  }
  if (rule.patterns) out.patterns = rule.patterns;
  return out;
}
function expand(patterns, self, acc = [], seen = new Set()) {
  for (const p of patterns || []) {
    let rule = p;
    if (p.include) {
      if (seen.has(p.include)) continue;
      seen.add(p.include);
      rule = p.include === "$self" ? { patterns: grammar.patterns } : grammar.repository[p.include.slice(1)];
      if (!rule) continue;
      if (!rule.match && !rule.begin) { expand(rule.patterns, self, acc, seen); continue; }
    } else if (!p.match && !p.begin) { expand(p.patterns, self, acc, seen); continue; }
    acc.push(compileRule(rule));
  }
  return acc;
}
const ROOT = expand(grammar.patterns);
const inner = new Map(); // a begin/end rule -> its expanded patterns
function patternsOf(rule) {
  if (!rule) return ROOT;
  if (!inner.has(rule)) inner.set(rule, expand(rule.patterns));
  return inner.get(rule);
}

function exec(re, line, pos) {
  re.lastIndex = pos;
  const m = re.exec(line);
  return m && m.index === pos ? m : null;
}

// the segments [end, style] of a match: captured groups get their scope, the rest the rule's
function segments(m, pos, name, captures) {
  const base = styleOf(name), segs = [];
  const whole = captures && captures["0"] ? styleOf(captures["0"].name) || base : base;
  let at = pos;
  if (captures && m.indices) {
    for (let g = 1; g < m.length; g++) {
      const c = captures[String(g)];
      if (!c || !m.indices[g]) continue;
      const [s, e] = m.indices[g];
      if (s < at) continue;
      if (s > at) segs.push([s, whole]);
      if (e > s) segs.push([e, styleOf(c.name) || whole]);
      at = e;
    }
  }
  const end = pos + m[0].length;
  if (end > at) segs.push([end, whole]);
  return segs;
}

export const parser = {
  name: "hugin",
  startState: () => ({ stack: [], pending: [] }),
  copyState: (s) => ({ stack: s.stack.slice(), pending: s.pending.slice() }),
  token(stream, state) {
    if (state.pending.length) {
      const [end, style] = state.pending.shift();
      stream.pos = end;
      return style;
    }
    const line = stream.string, pos = stream.pos;
    const top = state.stack[state.stack.length - 1];
    if (top) {
      const m = exec(top.end, line, pos);
      if (m) {
        state.stack.pop();
        return emit(stream, state, segments(m, pos, top.name, top.endCaptures));
      }
    }
    for (const rule of patternsOf(top)) {
      if (rule.match) {
        const m = exec(rule.match, line, pos);
        if (m && m[0].length) return emit(stream, state, segments(m, pos, rule.name, rule.captures));
      } else if (rule.begin) {
        const m = exec(rule.begin, line, pos);
        if (m && m[0].length) {
          state.stack.push(rule);
          return emit(stream, state, segments(m, pos, rule.name, rule.beginCaptures));
        }
      }
    }
    stream.next();
    return top ? styleOf(top.name) : null;
  },
};

function emit(stream, state, segs) {
  const [end, style] = segs.shift();
  state.pending.push(...segs);
  stream.pos = end;
  return style;
}

const tags = Object.fromEntries(CLASSES.map((c) => [c, Tag.define()]));
export const huginLanguage = StreamLanguage.define({ ...parser, tokenTable: tags });
export const huginHighlight = syntaxHighlighting(
  HighlightStyle.define(CLASSES.map((c) => ({ tag: tags[c], class: "hg-" + c })))
);
