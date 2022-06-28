---------------------------- MODULE FunUse --------------------------

EXTENDS FiniteSets, Constants

CONSTANT
    \* @type: Set(Int);
    Values

VARIABLE
    \* @type: Int -> Int;
    fun

Init ==
    fun = [x \in Values |-> x]

Inc ==
    \E x \in Values :
        /\ x \in DOMAIN fun
        /\ fun[x] = x
        /\ fun' = [fun EXCEPT ![x] = x + 1]

Next ==
    Inc

=============================================================================
