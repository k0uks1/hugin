// Highlighting of Hugin code blocks for highlight.js 10, which mdBook bundles. It follows the TextMate
// grammar of the VS Code extension (editors/vscode/syntaxes/hugin.tmLanguage.json); a change to the
// lexical syntax updates both. mdBook highlights every block before this script runs, so the Hugin blocks
// are highlighted again here, now that the language is known.
(function () {
  "use strict";
  if (typeof hljs === "undefined") return;

  hljs.registerLanguage("hugin", function (hljs) {
    var ident = "[A-Za-z0-9_']*";
    var comment = hljs.COMMENT("\\(\\*", "\\*\\)", { contains: ["self"] });
    var string = {
      className: "string",
      begin: '"',
      end: '"',
      contains: [{ className: "subst", begin: '\\\\(u\\{[0-9A-Fa-f]{1,6}\\}|["\\\\nt])' }],
    };
    var number = { className: "number", begin: "\\b\\d+(\\.\\d+([eE][+-]?\\d+)?)?\\b", relevance: 0 };
    var directive = { className: "meta", begin: "%[a-z]" + ident };
    var ruleName = { className: "symbol", begin: "@[a-z]" + ident };
    // the head of an item, which a declaration declares and a clause, fact or rule defines: its first name
    // in column 0 or after the period of an item on the same line (`expr : type. typ : type.`); and an
    // indented `name : …` or `name … =` (a member of a module body)
    var notKeyword = "(?!(where|not|as|with|type|rel|prop|data|count|sum|min|max)(?![\\w']))";
    var head = {
      className: "title",
      variants: [
        { begin: "(^|(?<=\\.[ \\t]))[ \\t]*" + notKeyword + "[a-z]" + ident + "(?![\\w']|\\.[a-z])" },
        { begin: "^[ \\t]+[a-z]" + ident + "(?=[ \\t]*(:(?!-)|=))" },
      ],
      relevance: 0,
    };
    // the universes `Type`, `Type₁`, …
    var universe = { className: "type", begin: "\\bType[\u2080-\u2089]*(?![\\w'])" };
    var variable = { className: "variable", begin: "\\b[A-Z_]" + ident, relevance: 0 };
    // typed holes `?` and `?name` (not `?-`), splices `$x` and `$..xs`, the lift `⇑`
    var meta = { className: "template-variable", begin: "\\?(?!-)" + ident + "|\\$(\\.\\.)?|⇑" };
    var operator = { className: "built_in", begin: ":-|\\?-|->|<:|::", relevance: 0 };
    var parens = { begin: "\\(", end: "\\)", contains: [] };
    // reflection quotes `'( … )`: parentheses nest inside, and the quoted code is highlighted as code
    var quote = { begin: "'\\(", end: "\\)", contains: [] };
    var items = [comment, string, number, directive, ruleName, head, quote, meta, universe, variable, operator];
    parens.contains = [parens].concat(items);
    quote.contains = [parens].concat(items);
    return {
      name: "Hugin",
      keywords: {
        $pattern: "[A-Za-z_][A-Za-z0-9_']*",
        keyword: "where not as with",
        type: "type rel prop data int float string",
        built_in: "count sum min max",
      },
      contains: items,
    };
  });

  document.querySelectorAll("code.language-hugin").forEach(function (block) {
    block.textContent = block.textContent;
    hljs.highlightBlock(block);
    block.classList.add("hljs");
  });
})();
