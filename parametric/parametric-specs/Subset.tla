---------------------------- MODULE Subset --------------------------

EXTENDS FiniteSets, Constants

CONSTANT
  \* @type: Set(Int);
  Values

VARIABLE
  \* @type: Set(Int);
  set

Init ==
  set = {}

SubsetAndAddOne ==
    /\ set \subseteq Values
    /\ \E x \in (Values \ set) : set' = set \union {x}

Next ==
    SubsetAndAddOne

=============================================================================
