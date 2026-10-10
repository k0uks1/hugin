// The playground's compiler worker (issue #58, docs/design/website.md 4.8 and 4.9). A classic worker: it
// loads hugin.js, the compiler linked by Scala.js (batch W4, a script bundle: Closure needs NoModule),
// and answers one request at a time. The page enforces the time budget by terminating this worker.
// The bundle declares the facade as a top-level `let Hugin`: a global binding of the script scope, which
// is not a property of `self`, so it is read by its name.
//
// Page -> worker: { id, op: "run" | "check", source, printAfter }   (printAfter: a phase name or "")
// Worker -> page: { ready: true, phases: [..] } once loaded, or { ready: false, error } if the bundle is
//                 missing; then { id, result } or { id, error } per request.
//
// `phases` are the phase names. `result` is the facade's answer (web/src/main/scala/hugin/web/Hugin.scala),
// normalised by `normalise` below; an answer `{ error }` (an invalid option, an internal error) is an error:
//   { diagnostics: [<JSON diagnostic, version 1, as `--error-format=json`>],
//     output: [<lines printed by `hugin run`>],
//     answers: [{ query, vars: [..], rows: [[..]] }],      // one per `?-` query
//     relations: [{ name, vars: [..], rows: [[..]] }],     // the `%output` relations
//     printed: "<program after printAfter>" | undefined,
//     tokens: [[text, [classes]]] | undefined }            // as `hugin highlight` returns them
// Only `adapt` and `normalise` know the facade's names.
"use strict";

let api = null;
try {
  importScripts("hugin.js");
  /* global Hugin */
  api = typeof Hugin !== "undefined" ? Hugin : self.Hugin;
  if (!api || typeof api.run !== "function") throw new Error("hugin.js defines no Hugin facade");
  postMessage({ ready: true, phases: phases() });
} catch (e) {
  postMessage({ ready: false, error: String(e && e.message ? e.message : e) });
}

function phases() {
  try {
    const p = typeof api.phases === "function" ? api.phases() : api.phases;
    // [{ name, description }] (or plain names)
    return Array.from(typeof p === "string" ? JSON.parse(p) : p || []).map((x) => (typeof x === "string" ? x : x.name));
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
  if (r.error) throw new Error(r.error);
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
