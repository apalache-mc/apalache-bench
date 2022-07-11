-------------------- MODULE MC3_consensus_forall -----------------------------
Node == { "1_OF_N", "2_OF_N", "3_OF_N" }

Quorum == {
    {"1_OF_N", "2_OF_N"},
    {"1_OF_N", "3_OF_N"},
    {"2_OF_N", "3_OF_N"}
}

Value == { "1_OF_V", "2_OF_V" }

VARIABLE 
    \* @type: Set(<<N, N>>);
    vote_request_msg,
    \* @type: N -> Bool;
    voted,
    \* @type: Set(<<N, N>>);
    vote_msg,
    \* @type: Set(<<N, N>>);
    votes,
    \* @type: N -> Bool;
    leader,
    \* @type: Set(N);
    voting_quorum,
    \* @type: Set(<<N, V>>);
    decided

INSTANCE consensus_forall
===============================================================================
