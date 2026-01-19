# User Guide CLI

This section of the documentation describes how to use and configure the TACO
CLI. This page will give you a quick start guide and you can find:

- details on how to install TACO on the page [](./usage-cli/install.md)
- an overview and detailed guide for all CLI commands in section
  [](./usage-cli/commands.md).
- a guide on how to write specifications in the (extended) ByMC format
  (i.e., as `.ta`, `.eta` files) in section [](./usage-cli/bymc-specification.md)
- a guide on how to write specifications in TLA+
  (i.e., as `.tla` files) in section [](./usage-cli/tla-specification.md)
- an introduction to TACO's advanced configuration options (like how to use it
  with custom SMT solvers) in section [](./usage-cli/advanced-configuration.md).

## Quick Start

This guide will assume you already installed TACO. You can find information on
how to install TACO on your specific system on the
[installation page](./usage-cli/install.md).

You can test whether TACO was successfully installed by using:

```bash
taco-cli --help
```

The help message will already give you an overview of all of TACO's commands. In
general, if you are unsure about the command syntax or specific options, you can
always append the `--help` flag and get an overview over the supported options
by the specific command.

The most important command of TACO is the `check` command, which starts the
model checker. To run this command, we first need an example to check.
We can copy the example from the
[](./usage-cli/bymc-specification.md#full-specification) and paste it into a
file, named for example `SRB.ta`.

Then we can let TACO check it by executing:

```bash
taco-cli check ./SRB.ta
```

TACO now automatically selects a configuration depending on the input file and
the dependencies available on your system. If you want to select a specific
model checker or SMT solver refer to [](./usage-cli/commands.md) for a complete
list of options.

For our example, TACO's output should look similar to:

```bash
12:18:22 - INFO - Welcome to the TACO model checker!
12:18:22 - INFO - Parsed threshold automaton with the name 'SRB' from the input file
12:18:22 - INFO - Threshold automaton has 5 locations and 8 rules
12:18:22 - INFO - Preprocessor 'DropSelfLoops' on 'SRB-validity' removed 0 of 8 rules: Removed rules are self-loops that do not update any shared variable.
12:18:23 - INFO - Preprocessor 'ReplaceTrivialGuardsSMT' on 'SRB-validity' replaced 0 trivial guards
12:18:23 - INFO - Starting to check property 'validity', which requires 5 model checker run(s).
12:18:23 - INFO - The error graph is empty.
12:18:23 - INFO - The error graph is empty.
12:18:23 - INFO - The error graph is empty.
12:18:23 - INFO - The error graph is empty.
12:18:23 - INFO - The error graph is empty.
12:18:23 - INFO - Threshold automaton satisfies all properties. The protocol is safe.
12:18:23 - INFO - Finished model checking. Goodbye!
```

In this case, there was only one property `validity` to check, which the
protocol satisfies and therefore TACO reports the protocol as safe.

In addition to the number of locations and rules, TACO also reports statistics
of the preprocessing and how many individual runs are required to verify each
property.

In this case, TACO will have selected the `zcs` model checker which needs 5 runs
to verify the property validity. These runs are required because the `zcs` model
checker needs to check all possible abstract interval orderings
(see [](alg:bdd)).

We can also do a sanity check and verify that `AC` is reachable at all by adding
the property:

```ta
reach_ac: [](AC == 0);
```

and run TACO on it. Then TACO finds a counter example:

```bash
14:11:31 - INFO - Counter example to property 'reach_ac': Path of threshold automaton SRB-reach_ac:
parameters: f : 0, n : 1, t : 0
Configuration 0: locations: (AC : 0, RV0 : 0, SE : 0, V0 : 0, V1 : 1), variables: (nsnt : 0, rec : 0)
        |
        |rule: 1 applied 1 times
        V
Configuration 1: locations: (AC : 0, RV0 : 0, SE : 1, V0 : 0, V1 : 0), variables: (nsnt : 1, rec : 1)
        |
        |rule: 3 applied 1 times
        V
Configuration 2: locations: (AC : 1, RV0 : 0, SE : 0, V0 : 0, V1 : 0), variables: (nsnt : 1, rec : 1)

14:11:31 - INFO - The protocol is unsafe.
```

Now you can start experimenting on your own examples!
