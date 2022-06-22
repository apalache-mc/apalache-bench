---------------- MODULE MC3_toy_consensus_epr -----------------------------
Node == { "1_OF_N", "2_OF_N", "3_OF_N" }

Quorum == {
    {"1_OF_N", "2_OF_N"},
    {"1_OF_N", "3_OF_N"},
    {"2_OF_N", "3_OF_N"}
}

Value == { "1_OF_V", "2_OF_V" }

VARIABLES
    \* @type: Set(N);
    voted,
    \* @type: Set(<<N, V>>);
    vote,
    \* @type: Set(V);
    decided

INSTANCE toy_consensus_epr
===============================================================================
