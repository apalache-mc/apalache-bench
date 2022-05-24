--------------- MODULE MC3_toy_consensus_forall -----------------------------
Node == { "1_OF_N", "2_OF_N", "3_OF_N" }

Value == { "1_OF_V", "2_OF_V" }

Nil == "Nil_OF_V"

VARIABLES
    \* @type: N -> Bool;
    voted,
    \* @type: N -> V;
    vote,
    \* @type: Set(V);
    decided

INSTANCE toy_consensus_forall
===============================================================================
