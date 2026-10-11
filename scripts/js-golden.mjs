// Runs the golden tests that need no file system through the browser bundle (`sbt web/bundle`) in Node:
//   - every single-file tests/run program (no .facts file, no import other than std/): the rendered
//     diagnostics, as `// ` comments, and Hugin.run's `output` must equal X.check, as GoldenTests builds it
//     from `hugin run` (X.flags translated to options);
//   - every tests/json program: Hugin.check's diagnostics must equal the JSON lines of X.check;
//   - the highlighting, the editor's analysis and completion (Hugin.highlight, Hugin.analyse,
//     Hugin.complete, Hugin.actions, Hugin.expansion) on small programs;
// and prints the bundle's size. Usage, from the repository root: node scripts/js-golden.mjs [web/target/bundle]
import fs from 'node:fs';
import path from 'node:path';
import vm from 'node:vm';
import zlib from 'node:zlib';
import { isDeepStrictEqual } from 'node:util';
import { pathToFileURL } from 'node:url';

const dir = process.argv[2] ?? 'web/target/bundle';
const { Hugin } = await import(pathToFileURL(path.resolve(dir, 'hugin.mjs')).href);
const failures = [];
const fail = (name, message) => failures.push(`${name}: ${message}`);

// the classic script defines the same global (it is what a classic worker loads)
const classic = vm.createContext({});
vm.runInContext(fs.readFileSync(path.join(dir, 'hugin.js'), 'utf8') + '\n;globalThis.Hugin = Hugin;', classic);
if (typeof classic.Hugin?.run !== 'function') fail('hugin.js', 'does not define Hugin.run');

// ... and Hugin.serveWorker() makes a worker answer messages (WorkerMain)
const posted = [];
const worker = vm.createContext({ WorkerGlobalScope: function () {}, postMessage: (m) => posted.push(m), onmessage: null });
vm.runInContext(fs.readFileSync(path.join(dir, 'hugin.js'), 'utf8') + '\n;Hugin.serveWorker();', worker);
worker.onmessage?.({ data: { id: 7, op: 'run', source: 'p : int -> rel.\np 1.\n?- p X.\n' } });
worker.onmessage?.({ data: { id: 8, op: 'frobnicate' } });
const [ready, answer, refusal] = posted;
if (answer?.result?.relations?.length !== 0) fail('worker', 'relations shown with a query: ' + JSON.stringify(answer));
const rel = JSON.parse(Hugin.run('p : int -> rel.\np 2.\np 1.\n'));
if (JSON.stringify(rel.relations) !== '[{"name":"p","vars":[],"rows":[["1"],["2"]]}]') fail('relations', JSON.stringify(rel));
if (!ready?.ready) fail('worker', 'no ready message');
if (answer?.id !== 7 || answer.result?.answers?.[0]?.rows?.[0]?.[0] !== '1') fail('worker', 'unexpected answer ' + JSON.stringify(answer));
if (refusal?.id !== 8 || !/unknown op/.test(refusal.result?.error)) fail('worker', 'unknown op not refused: ' + JSON.stringify(refusal));

/** The options of the command-line flags used in tests (X.flags). */
function options(flags, file) {
  const o = { file, lints: {} };
  const args = flags.split(/\s+/).filter(Boolean);
  for (let i = 0; i < args.length; i++) {
    const a = args[i];
    if (a === '--print-after') (o.printAfter ??= []).push(...args[++i].split(','));
    else if (a === '--all-relations') o.allRelations = true;
    else if (a === '--explain-termination') o.explainTermination = true;
    else if (a === '-A' || a === '-W' || a === '-D') o.lints[args[++i]] = { '-A': 'allow', '-W': 'warn', '-D': 'deny' }[a];
    else throw new Error(`${file}: flag ${a} has no option in scripts/js-golden.mjs`);
  }
  return o;
}

/** The diagnostics as `hugin run` renders them on stderr (with the summary line), as `// ` comments. */
function comments(diagnostics) {
  if (!diagnostics.length) return '';
  const count = (level) => diagnostics.filter((d) => d.level === level).length;
  const parts = [['error', count('error')], ['warning', count('warning')]].filter(([, n]) => n > 0).map(([w, n]) => `${n} ${w}${n === 1 ? '' : 's'}`);
  const lines = (diagnostics.map((d) => d.rendered).join('\n') + '\n' + parts.join(', ') + ' found').split('\n');
  return lines.map((l) => '// ' + l).join('\n') + '\n';
}

const read = (f) => (fs.existsSync(f) ? fs.readFileSync(f, 'utf8') : null);
const programs = (d) => fs.readdirSync(d).filter((f) => f.endsWith('.hgn')).sort().map((f) => path.join(d, f));
const times = [];

function call(fn, file, flags) {
  const started = performance.now();
  // the options as JSON text, as the playground's worker passes them
  const result = JSON.parse(Hugin[fn](fs.readFileSync(file, 'utf8'), JSON.stringify(options(flags, file))));
  times.push([performance.now() - started, file]);
  if (result.error) throw new Error(result.error);
  return result;
}

let run = 0, skipped = 0;
for (const file of programs('tests/run')) {
  const base = file.slice(0, -'.hgn'.length);
  const source = fs.readFileSync(file, 'utf8');
  if (fs.existsSync(base + '.facts') || /%(import|use)\s+"(?!std\/)/.test(source)) { skipped++; continue; }
  run++;
  try {
    const result = call('run', file, read(base + '.flags') ?? '');
    const actual = comments(result.diagnostics) + result.output.map((l) => l + '\n').join('');
    if (!result.ok) fail(file, 'not ok:\n' + result.diagnostics.map((d) => d.rendered).join('\n'));
    else if (actual !== read(base + '.check')) fail(file, 'output differs from ' + path.basename(base) + '.check:\n' + actual);
  } catch (e) { fail(file, String(e)); }
}

let json = 0;
for (const file of programs('tests/json')) {
  const base = file.slice(0, -'.hgn'.length);
  json++;
  try {
    const result = call('check', file, read(base + '.flags') ?? '');
    const expected = read(base + '.check').split('\n').filter(Boolean).map((l) => JSON.parse(l));
    if (!isDeepStrictEqual(result.diagnostics, expected)) fail(file, 'diagnostics differ:\n' + JSON.stringify(result.diagnostics));
  } catch (e) { fail(file, String(e)); }
}

// the highlighting (Hugin.highlight, and `tokens` in run's answer): runs that cover the program, with the
// semantic classes of `hugin highlight`
const hlSource = 'edge : int -> int -> rel.\nedge 1 2.\npath : int -> int -> rel.\npath X Y :- edge X Y.\n';
const hl = JSON.parse(Hugin.highlight(hlSource));
const cls = (text) => hl.tokens?.find((r) => r[0] === text)?.[1] ?? [];
if (hl.tokens?.map((r) => r[0]).join('') !== hlSource) fail('highlight', 'the runs do not cover the program: ' + JSON.stringify(hl));
else if (!cls('path').includes('function') || !cls('X').includes('variable') || !cls('int').includes('type')) fail('highlight', 'unexpected classes: ' + JSON.stringify(hl.tokens));
if (JSON.stringify(JSON.parse(Hugin.run(hlSource)).tokens) !== JSON.stringify(hl.tokens)) fail('highlight', 'run and highlight disagree');

// the editor's analysis (Hugin.analyse, and `info` in run's answer): the highlighting and the annotation
// table, in UTF-16 offsets; the session's database makes a repeated call free
const an = JSON.parse(Hugin.analyse(hlSource));
const at = (needle, n = 0) => { let i = -1; for (let k = 0; k <= n; k++) i = hlSource.indexOf(needle, i + 1); return i; };
const nameAt = (off) => an.info?.names?.find((n) => n[0] === off);
const use = nameAt(at('edge X'));
if (JSON.stringify(an.tokens) !== JSON.stringify(hl.tokens)) fail('analyse', 'analyse and highlight disagree');
else if (!use || use[5] !== at('edge :') || nameAt(at('edge :'))?.[4] !== 1 || nameAt(at('edge :'))?.[3] !== use[3])
  fail('analyse', 'unexpected names: ' + JSON.stringify(an.info));
else if (an.info.hovers[use[2]]?.[0] !== 'relation edge : int -> int -> rel') fail('analyse', 'unexpected hover: ' + JSON.stringify(an.info.hovers));
if (JSON.stringify(JSON.parse(Hugin.run(hlSource)).info) !== JSON.stringify(an.info)) fail('analyse', 'run and analyse disagree');
const lib = JSON.parse(Hugin.analyse('%use "std/graph".\nc : type.\nr : c -> c -> rel.\n%input r.\nt = tc { node = c, edge = r }.\n'));
if (!lib.info?.names?.some((n) => JSON.stringify(n[5]) === '["std/graph","tc"]')) fail('analyse', 'no library target: ' + JSON.stringify(lib.info));

// completion (Hugin.complete): the identifier being typed, the candidates, the ranking by the expected type
const cSource = 'nat : Type.\nzero : nat.\nsuc : nat -> nat.\nsize : nat -> int.\nsize zero = 0.\nquad : nat -> nat.\nquad Nat = s.\n';
const cOff = cSource.indexOf('= s.') + 3;
const comp = JSON.parse(Hugin.complete(cSource, cOff));
const suc = comp.items?.find((i) => i.label === 'suc');
if (comp.from !== cOff - 1 || !comp.ranked || !suc?.fits || suc.kind !== 'metaDefinition' || comp.items.find((i) => i.label === 'size')?.fits)
  fail('complete', 'unexpected completions: ' + JSON.stringify(comp));
worker.onmessage?.({ data: { id: 9, op: 'complete', source: cSource, offset: cOff } });
if (posted.at(-1)?.result?.from !== cOff - 1) fail('worker', 'complete: ' + JSON.stringify(posted.at(-1)));

// actions (Hugin.actions): a split at the cursor, in UTF-16 offsets
const aSource = 'nat : Type.\nzero : nat.\nsuc : nat -> nat.\ndouble : nat -> nat.\ndouble N = suc (suc N).\n';
const aOff = aSource.indexOf('N = suc');
const acts = JSON.parse(Hugin.actions(aSource, aOff, aOff));
const split = acts.actions?.find((a) => a.title === 'Split on `N`');
const clause = aSource.indexOf('double N');
if (split?.kind !== 'rewrite' || split.edits[0]?.from !== clause || split.edits[0]?.to !== aSource.length - 1 || !split.edits[0].insert.startsWith('double zero'))
  fail('actions', 'unexpected actions: ' + JSON.stringify(acts));
worker.onmessage?.({ data: { id: 10, op: 'actions', source: aSource, from: aOff, to: aOff } });
if (!posted.at(-1)?.result?.actions?.length) fail('worker', 'actions: ' + JSON.stringify(posted.at(-1)));

// the expansion (Hugin.expansion) of a functor application, and the inlay hints of the table
const eSource = 'p : int -> rel.\n%input p.\nmk (r : int -> rel) = { s : int -> rel. s X :- r X. }.\nm = mk p.\n%output m.s.\n';
const exp = JSON.parse(Hugin.expansion(eSource, eSource.indexOf('mk p')));
if (!exp.text?.includes('m.s X :- p X.')) fail('expansion', 'unexpected expansion: ' + JSON.stringify(exp));
if (JSON.parse(Hugin.expansion(eSource, 0)).text !== null) fail('expansion', 'an expansion where there is none');
const hints = JSON.parse(Hugin.analyse('ident : A -> A = [x] x.\nthree : int = ident 3.\n')).info?.hints;
if (!hints?.some((h) => h[1] === '{int}' && h[3] === 'implicit')) fail('analyse', 'no implicit hint: ' + JSON.stringify(hints));

const phases = JSON.parse(Hugin.phases());
if (!phases.some((p) => p.name === 'elaborate')) fail('phases', 'no phase `elaborate`');
const bad = JSON.parse(Hugin.run('x.', { printAfter: 'nonsense' }));
if (bad.error !== 'unknown phase `nonsense`') fail('options', 'an unknown phase is not reported: ' + JSON.stringify(bad));

const bytes = fs.readFileSync(path.join(dir, 'hugin.js'));
const kb = (n) => (n / 1024).toFixed(0) + ' KB';
const size = `bundle hugin.js: ${kb(bytes.length)} raw, ${kb(zlib.gzipSync(bytes, { level: 9 }).length)} gzip, ` +
  `${kb(zlib.brotliCompressSync(bytes).length)} brotli`;
times.sort((a, b) => b[0] - a[0]);
const total = times.reduce((s, t) => s + t[0], 0);
const summary = [
  `tests/run: ${run} run through the bundle (${skipped} skipped: facts files or imports); tests/json: ${json}`,
  `time: ${(total / 1000).toFixed(1)} s in all; slowest ${times.slice(0, 3).map((t) => `${t[1]} ${t[0].toFixed(0)} ms`).join(', ')}`,
  size,
  failures.length ? `${failures.length} FAILED` : 'all passed'
];
console.log(summary.join('\n'));
if (process.env.GITHUB_STEP_SUMMARY) fs.appendFileSync(process.env.GITHUB_STEP_SUMMARY, '### Browser build\n\n' + summary.map((s) => `- ${s}`).join('\n') + '\n');
for (const f of failures) console.error('\n' + f);
if (run < 50) { console.error(`only ${run} tests/run programs ran; expected at least 50`); process.exit(1); }
process.exit(failures.length ? 1 : 0);
