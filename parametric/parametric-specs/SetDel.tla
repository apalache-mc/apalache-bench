---------------------------- MODULE SetDel --------------------------

EXTENDS FiniteSets, Constants

CONSTANT
    \* @type: Set(Int);
    Values

VARIABLE
    \* @type: Set(Int);
    set

Init ==
    set = Values

DelOne ==
    \E x \in set : set' = set \ {x}

Next ==
    DelOne

Inv == set /= {}

=============================================================================
