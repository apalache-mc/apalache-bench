-------------------- MODULE MC3_simple_election -----------------------------
Acceptor == { "1_OF_N", "2_OF_N", "3_OF_N" }
Proposer == { "4_OF_N", "5_OF_N" }

Quorum == {
    {"1_OF_N", "2_OF_N"},
    {"1_OF_N", "3_OF_N"},
    {"2_OF_N", "3_OF_N"}
}

VARIABLES
    \* @type: Set(N);
    start,
    \* @type: Set(<<N, N>>);
    promise,
    \* @type: Set(N);
    leader

INSTANCE simple_election
================================================================================
