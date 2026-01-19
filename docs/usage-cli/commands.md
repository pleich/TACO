# Commands and Usage

In general, you will be able to get detailed documentation on a command or on
the options of a specific model checker by appending the `--help` / `-h` flag.

At the top level, you have the following options:

```bash
Usage: taco-cli [OPTIONS] <COMMAND>

Commands:
  check      Read the specification file and check the specified properties
  visualize  Read the specification file and visualize the threshold automaton
  translate  Translate from one specification file format to another one
  help       Print this message or the help of the given subcommand(s)

Options:
      --logger-config-file <LOGGER_CONFIG_FILE>
          Read the logger configuration from file. Logger configuration can be provided in the log4rs specification format
  -d, --debug
          Enable debug output. **Note**: This flag must be passed first, before any command
  -h, --help
          Print help
```

On this level TACO supports two commands:

- `visualize`: can be used to get a visualization of a threshold
  automaton, see [section `Visualize`](#visualize).
- `check`: is the command for executing the model checker, see
  [section `check`](#check).
- `translate`: can translate a TLA+ file (`.tla`) into a `.ta` file, see
  [section `Translate`](#translate)

Additionally, you can enable the debug output by passing the `--debug`
flag and configure the logger output using the `--logger-config-file`, see
[section Logger Configuration](#logger-configuration).

(check)=

## `check`

```bash
taco-cli check <INPUT_FILE>
```

The check command is used to verify a threshold automaton. If you already have a
threshold automaton as a `.ta`/`.eta` file, you can simply pass the file name
and TACO will determine a reasonable default configuration to verify the
specification.

However, you can also take full control and adjust many parameters. We will only
mention the most important ones. To see all possible parameters, use

```bash
taco-cli check --help
```

### Selecting a Model Checker

You can select a model checker by passing its name after the model checker. For
example, you can use

```bash
taco-cli check <INPUT_FILE> acs
```

to check the threshold automaton using the ACS Model Checker. The other options
are `zcs` for the 01-Counter System model checker and `smt` for the SMT model
checker.

Some model checkers have additional options that can be selected, like the ZCS
model checker. Again you can use the help menu (e.g. by using
`taco-cli check zcs --help`) to see all possible options with a brief
description.

### Selecting an SMT Solver

TACO uses SMT solvers for preprocessing, abstract interval ordering and for
model checking. TACO directly allows you to choose between `z3` and `cvc5` (note
though that they must be installed separately, see
[](./install.md#supported-smt-solvers)).
If both are installed on your system, TACO will by default select `z3`. If only
one of them is available, that solver will be selected by TACO.

You can also specify the solver to use by using the `--smt-solver`/`-s` flag.

Example (using cvc5):

```bash
taco-cli check <INPUT_FILE>  --smt-solver cvc5
```

### Selecting a BDD library

The ZCS model-checking algorithm uses Binary Decision Diagrams in its
decision procedure. TACO currently supports two libraries CUDD and OxiDD.
By default, TACO will use CUDD but you can select the library by using the
`--bdd`/`-b` flag.

#### OxiDD

[OxiDD](https://github.com/OxiDD/oxidd/tree/main) is a BDD library written fully
in Rust, with support for concurrent manipulation of BDDs. We use OxiDD by
default as compilation does not need any external dependencies and interfacing
with OxiDD does not require any unsafe code.

However, at the time of writing it does not yet support dynamic reordering
(support is planned to come in future versions), which is why it may be
beneficial to use CUDD on bigger examples.

Oxidd support can be enabled/disabled using the `oxidd` feature flag.

Example (using OxiDD):

```bash
taco-cli check <INPUT_FILE>  --bdd oxidd
```

#### CUDD

[CUDD](https://github.com/ivmai/cudd) is a C library for BDDs and is one of the
most well known and fully featured BDD libraries. It for example supports
dynamic reordering and convenient features like printing minterms. However, it
is not meant for concurrent manipulation of BDDS.

(visualize)=

## `visualize`

This command can generate a visual representation of a threshold automaton.
It will encode the given threshold automaton into a graph in the
[`DOT` language](https://graphviz.org/doc/info/lang.html).

If the graphviz library is present, TACO can also directly output `png` or `svg`
files. For more information, see [section Visualization: Installing Graphviz](#visualization-installing-graphviz)

(translate)=

## `translate`

TACO currently supports two input formats:

- the ByMC format (which you can find more information on in [](./bymc-specification.md))
- and a restricted version of TLA+ (defined in [](./tla-specification.md)).

TLA+ is a more open format that is very abstract from the internal TA model.
Therefore TACO also allows to output the threshold automaton specified in the
TLA+ file in the ByMC format (i.e. as a `.ta` file).

Details:

```bash
Translate from one specification file format to another one

Usage: taco-cli translate [OPTIONS] <INPUT_FILE> <OUTPUT_FILE>

Arguments:
  <INPUT_FILE>
          Location and name of the specification file

  <OUTPUT_FILE>
          Output file to save the translated output to

Options:
  -f, --format <INPUT_FORMAT>
          Format of the input specification file (if the file ending is not `.ta`, `.eta`, `.tla`)

          Possible values:
          - bymc: Specification file format introduced by ByMC (usually `.ta` or `.eta` files)
          - tla:  TLA+ specification (usually `.tla` files)

  -o, --output-format <OUT_FORMAT>
          Format to translate to (default: ByMC)

          Possible values:
          - bymc: Specification file format introduced by ByMC (usually `.ta` or `.eta` files)
          - tla:  TLA+ specification (usually `.tla` files)

          [default: bymc]

  -h, --help
          Print help (see a summary with '-h')
```
