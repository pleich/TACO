# TLA+ Specification Syntax

This document describes how to interact with the [TLA+](wiki:TLA%2B) to threshold automaton
(TA) translation.

If you are new to TLA+, you can learn more about it on the
[Learn TLA+ website](https://learntla.com/).

## Usage

TACO natively supports TLA+ files (that fall into TACO's translatable fragment)
as simply another input format. You simply use TACO on TLA+ files, either by
using the `--format tla` flag or simply by using the `.tla` file ending.

You can also use TACO to translate the TLA+ files into files in the `ByMC`
format by using the `translate` command.

Usage:

```bash
taco-cli translate <INPUT_FILE> -o bymc <OUTPUT_FILE>
```

This command will run the translation on the file `<INPUT_FILE>` and write
the output of the translation to the specified output file.

## Threshold Automata in TLA+

Since TLA+ is a very general language, our translation does only support a
subset. This section will walk you through an example threshold automaton
modeled in TLA+, and explain the TLA+ fragment supported by the translation.

We will use the threshold automaton depicted in [](#fig:ta-floodmin) as an
example. You can also find the encoding of the automaton into the ByMC / `.ta`
format [here](./ta-files.md#full-specification).

### Module Name

While not being mandatory, most TLA+ files declare a name of the module, i.e.
a name for the specification. This is usually done by writing:

```tla
------------------------------ MODULE SRB --------------------------------------
```

### EXTENDS

```tla
EXTENDS Integers, FiniteSets
```

In TLA+, `EXTENDS` is used to import different modules, e.g., `Integers` imports
the definition of integer numbers.

This field is only used to maintain compatibility with the original TLA+
language and does not cause the translation to load modules.

Other common examples that can be used in the context of threshold automata
include `Integers`, `Naturals`, `Sequence`, `FiniteSets` and `TLC`.

(constant)=

### CONSTANTS

```tla
CONSTANTS Processes, NbOfCorrProc, N, T, F
```

This part of the declaration declares the model constants in a TLA+
specification. When translating to TA, they are mapped to parameters, except for
two special constants:

- `Processes` which defines the set of process identifiers, and
- `NbOfCorrProc` which specifies the number of correct processes.

Both of these constants must always be declared, as they are used in the
specification file to model the actions processes can take.

Otherwise, this specification also declares the parameters `N`, `T` and `F`, as
common in threshold automata.

### ASSUME

```tla
ASSUME NbOfCorrProc = N - F
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0
```

The assume statement defines assumptions on the constants, i.e. assumptions
on the parameters of the threshold automaton.

Therefore, `ASSUME` is used to express the assumptions on the parameters, i.e.,
it is used to declare the resilience conditions of a threshold automaton.
The example in this case only has the resilience condition `N > 3 * T`.

Additionally, there must be an assume statement that describes the
relation between the parameters and the correct processes
(which is represented by `NbOfCorrProc`, see [section `CONSTANT`](#constant))
in the threshold automaton.

In our example this is done by the first constraint:

```tla
NbOfCorrProc = N - F
```

That is, in the modeled TA, the number of correct processes is given by $N - F$.
When working with the formal definition of TAs this function is often described
as $\mathcal{N}(N,T,F)$.

### VARIABLES

```tla
VARIABLES ProcessesLocations, nsnt, rDone
```

Variables in the TLA+ directly correspond to variables in the threshold
automaton and must be declared in a `VARIABLES` declaration.

Additionally, the variable `ProcessesLocation` must be declared. It is used
to store the current location of each process, i.e., it represents a map
from process identifiers (specified by the set `Processes`) to the location of
the corresponding process.

The locations of the threshold automaton are then specified by defining a type
constraint on `ProcessesLocation` in the `TypeOk` or correctness property
explained in the next section.

### TypeOk

```tla
TypeOk == rDone \in Nat
    /\ nsnt \in Nat
    /\ ProcessesLocations \in [Processes -> {"V0", "V1", "SE", "AC", "fRound"}]
```

The `TypeOk` invariant or correctness constraint is used in TLA+ to assert that
all declared variables are always part of the expected sets. It therefore
asserts that all constants always have the correct type.

When modelling a threshold automaton model, we have to declare the types
for the variables, which are always natural numbers (i.e., `Nat`).

Additionally, we have to declare the type for `ProcessesLocations`.
As explained in the previous section, `ProcessesLocations` is a map from process
identifier to locations, i.e., it must be part of the set of functions from the
set of process identifiers (`Processes`), to set of locations:

In the example:

```tla
ProcessesLocations \in [Processes -> {"V0", "V1", "SE", "AC", "fRound"}]
```

Implicitly, this constraint now also defines the set of locations of the threshold
automaton, here `{"V0", "V1", "SE", "AC", "fRound"}`.

### Init

```tla
Init == ProcessesLocations \in [Processes -> {"V0"}]
    /\ nsnt = 0
    /\ rDone = 0
```

`Init` declares the initial constraints, i.e., it declares which locations are
initial and with what evaluation the variables start.

Here, the constraint

```tla
ProcessesLocations \in [Processes -> {"V0"}]
```

describes that all processes are mapped to `"V0"`, i.e., it constrains all
processes to start in "V0". Note that in the derived threshold automaton,
faulty processes are no longer explicitly modeled, instead, only the correct
processes (which are defined by the constraint on ` NbOfCorrProc`) will be
modeled.

Next are constraints on the initial values of the shared variables in a
threshold automaton. In most cases, variables are initially 0, which is the case
for `nsnt` and `rDone` in our example.

### Rules

Rules can be specified by declaring an operator of the following form:

```tla
Rule0(p) == ProcessesLocations[p] = "V0"
    /\ nsnt >= T - F + 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "SE"]
    /\ nsnt' = nsnt + 1
    /\ UNCHANGED<<rDone>>
```

This operator is then translated into a rule of a threshold automaton with:

- **id**: `0`, is simply parsed from the name of the rule.
- **source location**: `V0` as specified by a constraint on the current
  location of `p`, in the example by the constraint
  ` ProcessesLocations[p] = "V0"`.
- **target location**: "SE", is specified by defining an update on the
  location of `p`, i.e., by
  `ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "SE"]`.
- **guard(s)**: Here `nsnt >= T - F + 1`, is simply a boolean constraint on the
  current evaluation of processes.
- **actions**: increment `nsnt` (`nsnt' = nsnt + 1`), `rDone` remains
  unchanged (`UNCHANGED << rDone >>`).

### Next

```tla
Next == \E p \in Processes: Rule0(p) \/ Rule1(p) \/ Rule2(p) \/ Rule3(p)
    \/ Rule4(p) \/ Rule5(p) \/ Rule6(p) \/ Rule7(p)
```

After having specified all the rule operators, we still need to define the
`Next` relation. In TLA+, the next definition describes what steps can be taken.
For threshold automata this is always some process executing a rule.
Therefore, `Next` is simply the disjunction over the rule operators.

### Spec (optional)

```tla
Spec == Init /\ [][Next]_<<ProcessesLocations, nsnt, rDone>>
```

Finally, a full specification in TLA+ can also declare a `Spec` which simply
describes that the initial constraints must hold in the initial
configuration and that the next configurations are derived by applying `Next` to
the location of processes `ProcessesLocations` and the shared variables `nsnt`,
`rDone`.

Specifying a `Spec` operator is optional for TACO and TLC. TLC also allows you
to specify a `NEXT` and `INIT` field instead.

### Specifications

The next part of the TLA+ specification describes the correctness
properties of the threshold automaton, in our example, the correctness
properties are defined by the operators:

```tla
NumInV1 == Cardinality({p \in Processes : ProcessesLocations[p] = "V1"})
NumInAC == Cardinality({p \in Processes : ProcessesLocations[p] = "AC"})

validity1 == NumInV1 = 0 => [](NumInAC = 0)
```

Here, we use the operators

```tla
NumInV1 == Cardinality({p \in Processes : ProcessesLocations[p] = "V1"})
NumInAC == Cardinality({p \in Processes : ProcessesLocations[p] = "AC"})
```

to define a helper operator that allows reasoning over the number of processes
in locations `V1` and `AC` respectively.

Then, we can express the correctness properties in $ELTL_{FT}$ using the newly
declared operators and the regular ELTL operators. For example

```tla
validity1 ==  NumInV1 = 0 => [](NumInAC = 0)
```

is translated to `(V1 = 0) -> [](AC = 0)`. Of course, the specifications can
also include constraints on the shared variables.

### Full Specification

```{code} tla
:linenos:
:caption: Full TLA+ specification for threshold automaton depicted in [](#fig:ta-floodmin)
------------------------------ MODULE SRB --------------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Processes, NbOfCorrProc, N, T, F

ASSUME NbOfCorrProc = N - F
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

VARIABLES ProcessesLocations, nsnt, rDone

TypeOk == rDone \in Nat
    /\ nsnt \in Nat
    /\ ProcessesLocations \in [Processes -> {"V0", "V1", "SE", "AC", "fRound"}]

Init == ProcessesLocations \in [Processes -> {"V0"}]
    /\ nsnt = 0
    /\ rDone = 0
--------------------------------------------------------------------------------
Rule0(p) == ProcessesLocations[p] = "V0"
    /\ nsnt >= T - F + 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "SE"]
    /\ nsnt' = nsnt + 1
    /\ UNCHANGED<<rDone>>
--------------------------------------------------------------------------------
Rule1(p) == ProcessesLocations[p] = "V0"
    /\ nsnt >= N - T - F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "AC"]
    /\ UNCHANGED<<nsnt, rDone>>
--------------------------------------------------------------------------------
Rule2(p) == ProcessesLocations[p] = "V1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "SE"]
    /\ nsnt' = nsnt + 1
    /\ UNCHANGED <<rDone>>
--------------------------------------------------------------------------------
Rule3(p) == ProcessesLocations[p] = "V1"
    /\ nsnt >= N - T - F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "AC"]
    /\ UNCHANGED<<nsnt, rDone>>
--------------------------------------------------------------------------------
Rule4(p) == ProcessesLocations[p] = "SE"
    /\ nsnt >= N - T - F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "AC"]
    /\ UNCHANGED<<nsnt, rDone>>
--------------------------------------------------------------------------------
Rule5(p) == ProcessesLocations[p] = "AC"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "fRound"]
    /\ rDone' = rDone + 1
    /\ UNCHANGED<<nsnt>>
--------------------------------------------------------------------------------
Rule6(p) == ProcessesLocations[p] = "fRound"
    /\ rDone >= N - F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "V1"]
    /\ nsnt' = 0
    /\ rDone' = 0
--------------------------------------------------------------------------------
Rule7(p) == ProcessesLocations[p] = "fRound"
    /\ rDone > 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "V1"]
    /\ UNCHANGED<<nsnt, rDone>>
--------------------------------------------------------------------------------

Next == \E p \in Processes: Rule0(p) \/ Rule1(p) \/ Rule2(p) \/ Rule3(p)
    \/ Rule4(p) \/ Rule5(p) \/ Rule6(p) \/ Rule7(p)

Spec == Init /\ [][Next]_<< ProcessesLocations,nsnt,rDone >>
--------------------------------------------------------------------------------

NumInV1 == Cardinality({p \in Processes : ProcessesLocations[p] = "V1"})
NumInAC == Cardinality({p \in Processes : ProcessesLocations[p] = "AC"})

validity1 == NumInV1 = 0 => [](NumInAC = 0)
================================================================================
```

## More Examples

We provide TLA+ models of all the "Small ByMC" benchmarks in the directory
`./examples/tla`. You can take a look at them and try them out, for
example using TLC.

### (Non-Parametric) Model Checking with TLC

Since our files are a TLA+ description of a threshold automaton, you can use TLC
(a model checker for TLA+, for more information and installation options
see
[Leslie Lamports TLA+ Homepage](https://lamport.azurewebsites.net/tla/tla.html))
to verify the correctness of the threshold automaton with a fixed amount of
processes.

To do so you will need to create a `cfg` file for TLC, that instantiates the
`CONSTANT` of the specification (which include the parameters of the threshold
automaton).

For example, a configuration for the `aba.tla` specification (which you can find
in the directory `tla-comp/examples/tla`) for checking the threshold automaton
with 7 processes and one faulty process requires the following configuration:

```{code} tla
:linenos:
:caption: Example configuration for TLC with 7 processes
CONSTANT
  Processes = { p0, p1, p2, p3, p4, p5, p6  }
  NbOfCorrProc = 5
  N = 6
  T = 1
  F = 1

SPECIFICATION
  Spec

INVARIANT TypeOk

PROPERTIES validity1
```

Explanation of the values:

- `Processes = { p0, p1, p2, p3, p4, p5, p6 }`: Processes is the set of process identifiers
- `NbOfCorrProc = 5`: `NbOfCorrProc` specifies the number of processes that are behaving correctly, here we use 5
- `N = 6`: is the parameter in the threshold automaton that specifies the number of processes, so in this case we have 6 processes
- `T = 1`: The upper bound on allowed faulty processes, here instantiated as 1
- `F = 1`: The actual number of faulty processes
- `PROPERTIES validity1`: Property to check, here `validity1`
