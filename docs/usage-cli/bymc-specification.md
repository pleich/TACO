# ByMC Specification Syntax

TACO mainly works on `.ta` or `.eta` files, which are very close to the actual
threshold automata model. You can find a full formal definition of the accepted
syntax in the [parser crate](./dev-docs.md) of TACO.

:::{note}
TACO inherits the syntax of the `.ta` files from [ByMC](https://github.com/konnov/bymc).
You can still find the original grammar [here](https://github.com/konnov/bymc/blob/master/bymc/doc/ta-format.md) in the ByMC repository.  
:::

This section will give you an introduction to the format by encoding the threshold automaton depicted in [](#fig:ta-floodmin). If you want to find out more about
the purpose of the individual components you can refer to the
[](../theoretical-background.tex) section.

## Skeleton

Every threshold automaton starts with an outer skeleton block which begins with
`ta` (or `skel` or `thresholdAutomaton`) followed by the name of the threshold
automaton.

For example, if we want to encode [](#fig:ta-floodmin) and name it `SRB`, we
would start by using:

```ta
// Outer Skeleton of the threshold automaton named `SRB`.
ta SRB {
    ...
}
```

## Declaration of Shared Variables

Next, we need to declare the components of the threshold automaton, starting
with the shared variables. In this case, our threshold automaton has two `nsnt`
and `rec`, which are declared using:

```ta
// shared variable declaration
shared nsnt, rec;
```

## Declaration of Parameters

Afterward, we can declare the parameters of the threshold automaton similarly:

```ta
// parameter declaration
parameters n, t, f;
```

## (Optional) Declaration of Macros

Even though not included in the official grammar, ByMC and many of the
benchmarks written for ByMC use macros for frequently used expressions. They
can be defined inside a `define` block:

```ta
define THRESH_0 == n - f;
define THRESH_1 == t + 1 - f;
```

Instead of writing `n - f` or `t + 1 - f` in the specification file, you can now
use `THRESH_0` or `THRESH_1` respectively.

## Assumptions / Resilience Condition

After the parameters have been declared, we need to specify the resilience
conditions ($RC$ in the formal definitions
[see](./background.tex)).

In this case, we have the resilience conditions

$$
n > 3 \cdot t \\
t \geq f \\
f \geq 0
$$

which are translated into individual statements separated by a `;`:

```ta
// Encoding of resilience conditions
assumptions (3) {
    n > 3 * t;
    t >= f;
    f >= 0;
}
```

## Declaring Locations

After the shared variables and parameters, as well as the resilience conditions
have been defined, we still have to declare the locations exist, which is done
in a `locations` block.

```ta
// Declaration of locations of the threshold automaton
locations (5) {
    V0: [0];
    V1: [1];
    RV0: [2];
    SE: [3];
    AC: [4];
}
```

Note that TACO does neither use the number of locations (i.e., the n in
`locations (n) {`) nor the indices of locations (i.e., the numbers in the `[]`
brackets). You could also just write `0` for TACO.
However, we decided to keep them to maintain compatibility with ByMC.

## Initial Conditions

The `inits` block in a `.ta` file has two main purposes:

- it declares the initial conditions on variables, and
- it declares which locations are initial

### Initial Variable Conditions

The initial variable conditions define with what values the variables start.
In most cases, we do assume that initially the variables are set to 0, which
is achieved for a variable `nsnt` by specifying

```ta
nsnt == 0;
```

### Initial Location Constraints

The inits block also allows you to define which locations of a threshold
automaton can be initial. When using the name of a location in the `inits`
block, you refer to the number of processes that are allowed in that initial
state.

Additionally, the `inits` block also defines the relation between the parameters
and the processes, which we model explicitly.
A threshold automaton only models the correct processes explicitly
(see [](../theoretical-background.tex)). In our case, the number of correct processes is
given by $n - f$, and we now want these $n - f$ processes to start in one of the
initial states.

Since the initial states in [](#fig:ta-floodmin) are `V1` and `V0` we can achieve
this with the constraint:

```ta
V1 + V0 == n - f; /* n-f correct processes in initial states */
```

or using the previously defined macro:

```ta
V1 + V0 == THRESH_0; /* n-f correct processes in initial states */
```

Additionally, you have to define that all other locations, for example `AC`,
**cannot** have any process starting in it, by writing:

```ta
// No process is in location `AC`
AC == 0;
```

### The Full `inits` Block

For [](#fig:ta-floodmin), the full `inits` block is then given by:

```ta
inits(6) {
    nsnt == 0;
    rec == 0;
    RV0 == 0;
    SE == 0;
    AC == 0;
    V1 + V0 == THRESH_0; /* n-f correct processes in initial states */
}
```

## Defining Rules

Next, we have to define how processes can move from one location to the other,
i.e., we need to declare the rules of the threshold automaton. This is done
inside a `rules` block.

### Example Rule

Let's, for example, define the rule from location `SE` to `V1` with the guard

$$
    (rec \geq n - f) \wedge (nsnt > t + 1 - f)
$$

that resets the variables `rec` and `nsnt`. In a `.ta` file we first have to
give the rule a unique id (lets say `6`) then the rule is specified as:

```ta
6: SE -> V1
    when ((rec >= n - f) && (nsnt > t + 1 - f))
    do { rec' := 0; nsnt' := 0; };
```

where `when` contains the rule guard and `do` specifies the update.
Note that the variable to be updated has an additional `'` and we use the
assignment operator `:=`.

Alternatively, the rule can be specified with the previously defined macros:

```ta
6: SE -> V1
    when ((rec >= THRESH_0) && (nsnt > THRESH_1))
    do { rec' := 0; nsnt' := 0; };
```

To specify an update like an increment, you can also refer to the old variable
value in the condition after the assignment. For example:

```ta
rec' := rec + 1;
```

specifies an increment of variable `rec` by one. You can find an encoding of all
the rules of [](#fig:ta-floodmin) in section [](#full-specification).

## Correctness Property

After having specified the full automaton, we also have to specify its
correctness properties. This is done inside a `specifications` block. To
specify a property `validity` in $ELTL_{FT}$ of the form

$$
(V1 == 0) \Rightarrow \square( AC == 0)
$$

we simply write:

```ta
validity:
    V1 == 0 -> [](AC == 0);
```

(full-specification)=

## Full Specification

If we put everything together, we get the full encoding of [](#fig:ta-floodmin) as:

```{code} ta
:linenos:
:caption:  Full ByMC specification for threshold automaton depicted in [](#fig:ta-floodmin)
ta SRB {
    shared nsnt, rec;

    parameters n, t, f;

    define THRESH_0 == n - f;
    define THRESH_1 == t + 1 - f;

    assumptions (3) {
        n > 3 * t;
        t >= f;
        f >= 0;
    }

    locations (5) {
        V0: [0];
        V1: [1];
        RV0: [2];
        SE: [3];
        AC: [4];
    }

    inits(6) {
        nsnt == 0;
        rec == 0;
        RV0 == 0;
        SE == 0;
        AC == 0;
        V1 + V0 == THRESH_0; /* n-f correct processes in initial states */
    }

    rules (8) {
        0: V0 -> RV0
            when (true)
            do { rec' := rec + 1; };
        1: V1 -> SE
            when (true)
            do { nsnt' := nsnt + 1; rec' := rec + 1; };
        2: RV0 -> SE
            when (nsnt >= THRESH_1)
            do {};
        3: SE -> AC
            when (nsnt >= n - t - f)
            do {};
        4: RV0 -> V0
            /* when ((rec >= n - f) && (nsnt > t + 1 - f)) */
            when ((rec >= THRESH_0) && (nsnt > THRESH_1))
            do {};
        5: RV0 -> V0
            when (rec == 0)
            do {};
        6: SE -> V1
            /* when ((rec >= n - f) && (nsnt > t + 1 - f)) */
            when ((rec >= THRESH_0) && (nsnt > THRESH_1))
            do { rec' := 0; nsnt' := 0; };
        7: SE -> V1
            when (rec == 0)
            do {};
    }

    specifications (1) {
        validity: V1 == 0 -> [](AC == 0);
    }
}
```
