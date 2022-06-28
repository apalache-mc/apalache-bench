---------------------------- MODULE SetAdd --------------------------
\* In this parametric example we have N values, and a set variable, initially empty.
\* At each step we can add one element to the set.
\* The invariant specifies that the set is not complete,
\* i.e., we ask whether a state where the set contains all the values is reachable.
\* This final configuration is reachable in exactly N steps.
\*
\*
\* check the spec with arguments --cinit=CInit<N> --length=<N>
\*
\* Andrey Kuprianov and Shon Feder, 2021

EXTENDS FiniteSets, Constants

CONSTANT
    \* @type: Set(Int);
    Values

VARIABLE
    \* @type: Set(Int);
    set

Init ==
    set = {}

AddOne ==
    \E x \in (Values \ set) : set' = set \union {x}

Next ==
    AddOne

Inv == set /= Values

=============================================================================
