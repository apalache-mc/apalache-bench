---------------------------- MODULE SetMap --------------------------

EXTENDS FiniteSets, Constants

CONSTANT
    \* @type: Set(Int);
    Values

VARIABLE
    \* @type: Set(Int);
    set

Init ==
    set = Values

MapOne ==
    set' = {x + 100 : x \in set}

Next ==
    MapOne

=============================================================================
