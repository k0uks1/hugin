// The playground's compiler worker (issue #58, docs/design/website.md 4.8 and 4.9). A classic worker: it
// loads hugin.js, the compiler linked by Scala.js (batch W4, a script bundle: Closure needs NoModule),
// and answers one request at a time. The page enforces the time budget by terminating this worker.
//
// Page -> worker: { id, op: "run" | "check", source, printAfter }   (printAfter: a phase name or "")
// Worker -> page: { ready: true, phases: [..] } once loaded, or { ready: false, error } if the bundle is
//                 missing; then { id, result } or { id, error } per request.
//
// `result` is the facade's answer, normalised by `normalise` below:
//   { diagnostics: [<JSON diagnostic, version 1, as `--error-format=json`>],
//     output: [<lines printed by `hugin run`>],
//     answers: [{ query, vars: [..], rows: [[..]] }],      // one per `?-` query
//     relations: [{ name, vars: [..], rows: [[..]] }],     // the `%output` relations
//     printed: "<program after printAfter>" | undefined,
//     tokens: [[text, [classes]]] | undefined }            // as `hugin highlight` returns them
// Only `adapt` knows the facade's names; it is the one place to change if W4's API differs.
"use strict";

let api = null;
try {
  importScripts("hugin.js");
  api = self.Hugin || self.hugin || (typeof self.run === "function" ? self : null);
  if (!api) throw new Error("hugin.js defines no Hugin facade");
  postMessage({ ready: true, phases: phases() });
} catch (e) {
  postMessage({ ready: false, error: String(e && e.message ? e.message : e) });
}

function phases() {
  try {
    const p = typeof api.phases === "function" ? api.phases() : api.phases;
    return Array.from(typeof p === "string" ? JSON.parse(p) : p || []);
  } catch (_) {
    return [];
  }
}

function adapt(op, source, printAfter) {
  const options = JSON.stringify({ printAfter: printAfter || null, file: "main.hgn" });
  const fn = op === "check" && typeof api.check === "function" ? api.check : api.run;
  return fn.call(api, source, options);
}

function list(x) {
  if (x == null) return [];
  if (typeof x === "string") return x === "" ? [] : x.replace(/\n$/, "").split("\n");
  return Array.from(x);
}

function normalise(raw) {
  const r = typeof raw === "string" ? JSON.parse(raw) : raw || {};
  const diagnostics = list(r.diagnostics).map((d) => (typeof d === "string" ? JSON.parse(d) : d));
  const table = (t) => ({ ...t, vars: list(t.vars || t.variables), rows: list(t.rows).map(list) });
  return {
    diagnostics,
    output: list(r.output || r.lines),
    answers: list(r.answers).map(table),
    relations: list(r.relations).map(table),
    printed: r.printed == null ? undefined : String(r.printed),
    tokens: r.tokens ? list(r.tokens) : undefined,
  };
}

onmessage = (e) => {
  const { id, op, source, printAfter } = e.data;
  if (!api) return postMessage({ id, error: "the compiler is not available" });
  try {
    postMessage({ id, result: normalise(adapt(op, source, printAfter)) });
  } catch (err) {
    postMessage({ id, error: String(err && err.message ? err.message : err) });
  }
};
