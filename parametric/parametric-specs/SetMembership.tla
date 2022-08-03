---------------------------- MODULE SetMembership --------------------------

EXTENDS FiniteSets, Constants

CONSTANT
  \* @type: Set(Int);
  Values

VARIABLE
  \* @type: Set(Int);
  set

Init ==
  set = {0}

AddOne ==
    \E x \in (Values \ set) : set' = set \union {x}

Membership ==
    /\ \E x \in Values : x \in set
    /\ UNCHANGED << set >>

Next ==
    \/ AddOne
    \/ Membership

Inv == TRUE

=============================================================================
