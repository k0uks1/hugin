# The command line

The program `hugin` compiles, runs and inspects Hugin programs. This chapter lists its commands and
options; `hugin --help` prints the same list.

```text
hugin <command> [<file.hgn>] [options]
```

## Commands

| command | what it does |
|---|---|
| `run <file.hgn>` | compiles and evaluates the program, and prints its output relations and the answers to its queries ([Output relations](object/io.md#output-relations)) |
| `check <file.hgn>` | compiles the program and reports its diagnostics, without evaluating it |
| `fix <file.hgn>` | applies the machine-applicable suggestions of the diagnostics to the file, until none is left |
| `phases` | lists the phases of the compiler |
| `explain <code>`, `explain --list` | prints the explanation of a diagnostic code ([Error index](errors/index.md)), or lists every code |
| `query <file.hgn> <request> [<line>:<col>]` | answers a request of an editor: `hover`, `definition`, `references` and `completions` at a position, `symbols` and `diagnostics` of the file |
| `repl [<file.hgn>…]` | starts an interactive session; `--batch` reads it from standard input without prompts, `--echo` also writes each input after its prompt |
| `lsp` | runs the language server, which speaks the Language Server Protocol on standard input and output |

The exit code is 0 on success, 1 if compilation, input or evaluation reported an error, and 2 if the
command line is malformed or the program file does not exist.

## Options of `run` and `check`

| option | effect |
|---|---|
| `--facts <file>` | loads the facts of input relations from a facts file ([Input facts](object/io.md#input-facts)); repeatable |
| `--all-relations` | prints the facts of every relation, also of constructors and demand relations |
| `--export-proofs <file>` | with `run`: writes the proofs of the derived facts to the file ([Proof export](object/io.md#proof-export)) |
| `--proof-format trees\|ordered-graph` | with `--export-proofs`: one proof tree per fact (the default) or one ordered proof graph |
| `--stats` | prints the time of each compiler phase and the number of rounds of each component |
| `--explain-termination` | prints the termination argument of every recursive component ([Termination](object/termination.md)) |
| `--safe` | rejects every postulate of the program and of the files it imports ([E0925](errors/E0925.md); [Consistency](meta/consistency.md#postulates)) |
| `--print-assumptions <name>` | prints the postulates and trusted primitives that the constant `<name>` depends on; repeatable ([Consistency](meta/consistency.md#assumptions)) |
| `--print-after <phase>,…` | prints the program after the phases (`all` for every phase) |
| `--stop-after <phase>` | stops compilation after the phase |
| `--no-prelude` | does not include the [prelude](prelude.md) |

## Options for diagnostics

| option | effect |
|---|---|
| `-W <lint>`, `-A <lint>`, `-D <lint>` | reports the lint as a warning, allows it, or reports it as an error ([Notation](notation.md)); repeatable, the last option for a lint wins |
| `--deny-warnings` | reports every lint that is a warning as an error |
| `--error-format human\|json` | renders diagnostics for people (the default) or prints one JSON object per line |
| `--color`, `--no-color` | colours diagnostics, or does not |
