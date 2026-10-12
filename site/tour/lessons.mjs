// The language tour (/tour/): one lesson per page, in this order. Each lesson has its text,
// site/tour/<file>.html, and its program, site/tour/<file>.hgn, whose output (`hugin run`, with
// <file>.flags if present) must equal <file>.check; a `wrong` variant, site/tour/<wrong>.hgn, must fail to
// compile with the diagnostics of <wrong>.check. TourExamplesSuite checks all of them in CI (`sbt test`);
// site/build.mjs renders the pages, and site/tour/tour.js makes the program on each page editable and
// checks it in the browser.
export const parts = [
  { id: "basics", title: "Basics", blurb: "Enough of the language to read the proofs: relations, rules, modules and the meta level." },
  { id: "proofs", title: "Proofs about programs", blurb: "Properties of Datalog programs stated as types, and proofs that the compiler checks." },
];

export const lessons = [
  { part: "basics", slug: "facts", file: "facts", title: "Relations and rules",
    summary: "Object types, relations, facts, and rules that derive new facts." },
  { part: "basics", slug: "queries", file: "queries", title: "Queries, negation, aggregates",
    summary: "Asking questions, and the two non-monotone features: negation and aggregates." },
  { part: "basics", slug: "modules", file: "functors", title: "Modules and functors",
    summary: "Programs parameterised by a signature: std/graph's tc, and instances of it." },
  { part: "basics", slug: "meta", file: "meta", title: "The meta level",
    summary: "Types as propositions, functions by clauses as proofs." },
  { part: "proofs", slug: "derivations", file: "derivations", title: "Derivations are values",
    summary: "The judgment P ⊢ r x y, and rule names as constructors and patterns." },
  { part: "proofs", slug: "transitivity", file: "transitivity", wrong: "transitivity-wrong", title: "Transitivity",
    summary: "The transitive closure of any graph is transitive, by induction on derivations." },
  { part: "proofs", slug: "symmetry", file: "symmetry", title: "Symmetry",
    summary: "Reachability in an undirected graph is symmetric, stated with relations as propositions." },
  { part: "proofs", slug: "equivalence", file: "equivalence", title: "Two programs, the same facts",
    summary: "A rewrite of tc derives exactly the facts of tc, as a lemma that every instance has." },
  { part: "proofs", slug: "soundness", file: "soundness", title: "An analysis over-approximates",
    summary: "Reachability on an abstracted graph covers every reached node." },
  { part: "proofs", slug: "negation", file: "negation", title: "Negation",
    summary: "A theorem about a relation defined with not, for every complete graph." },
  { part: "proofs", slug: "decide", file: "decide", wrong: "decide-wrong", title: "Proof by evaluation",
    summary: "Ground facts proved by running the program inside the type checker, and how far that goes." },
  { part: "proofs", slug: "certify", file: "certify", title: "Certified runs",
    summary: "Checking the output of a run against the semantics, and what is trusted." },
];
