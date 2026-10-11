// Completion in the playground (issue #147, docs/design/web-ide.md 6.1, batch P2): CodeMirror's
// autocompletion with an async source that asks the worker (`complete`) for the compiler's candidates at
// the cursor (hugin.ide.Completion: names in scope, members after `.`, labels in `c { … }`, directives
// after `%`, object syntax only inside a quote). Typing on filters locally while the identifier still
// matches (`validFor`); candidates whose result type fits the expected type come first. Ctrl-Space asks
// explicitly; typing an identifier or `.`, `{` or `%` asks on its own.
import { autocompletion, completionKeymap } from "@codemirror/autocomplete";

export { completionKeymap };

// hugin.ide.CandidateKind -> CodeMirror's completion types (the icon)
const TYPES = {
  directive: "keyword", variable: "variable", metaParameter: "variable", label: "property", relation: "function",
  constructor: "enum", struct: "class", objectType: "type", baseType: "type", typeDefinition: "type",
  formulaFunction: "method", metaDefinition: "namespace", other: "text",
};

const IDENT = /^[\w']*$/;
const TRIGGERS = ".{%";

// `ask(source, offset)` resolves to the worker's answer { version, from, items, ranked } or to null (no
// answer: the compiler is busy or unavailable, or the text changed meanwhile)
export function completion(ask) {
  return autocompletion({
    override: [
      async (ctx) => {
        const word = ctx.matchBefore(/[\w']*/);
        const before = word.from > 0 ? ctx.state.sliceDoc(word.from - 1, word.from) : "";
        if (!ctx.explicit && word.from === word.to && !TRIGGERS.includes(before || "-")) return null;
        const answer = await ask(ctx.state.doc.toString(), ctx.pos);
        if (!answer || ctx.aborted) return null;
        return {
          from: answer.from,
          validFor: IDENT,
          options: answer.items.map((c) => ({
            label: c.label,
            type: TYPES[c.kind] || "text",
            detail: c.detail === c.label ? undefined : c.detail,
            boost: answer.ranked && c.fits ? 50 : 0,
          })),
        };
      },
    ],
    icons: true,
    maxRenderedOptions: 200,
  });
}
