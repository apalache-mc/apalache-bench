------------------------ MODULE MC3_consensus_epr -----------------------------
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
    \* @type: N -> Set(N);
    votes,
    \* @type: N -> Bool;
    leader,
    \* @type: N -> Set(V);
    decided

INSTANCE consensus_epr
===============================================================================
