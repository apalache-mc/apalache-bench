---------------------------- MODULE SetFilter --------------------------

EXTENDS FiniteSets, Constants

CONSTANT
    \* @type: Set(Int);
    Values

VARIABLE
    \* @type: Set(Int);
    set

Init ==
    set = Values

FilterOne ==
    \E x \in set : set' = {y \in set : x /= y}

Next ==
    FilterOne

Inv == set /= {}

=============================================================================
