------------------ MODULE MC3_consensus_wo_decide -----------------------------
Node == { "1_OF_N", "2_OF_N", "3_OF_N" }

Quorums == {
    {"1_OF_N", "2_OF_N"},
    {"1_OF_N", "3_OF_N"},
    {"2_OF_N", "3_OF_N"}
}

VARIABLE
    \* @type: <<N, N>> -> Bool;
    vote_request_msg,
    \* @type: N -> Bool;
    voted,
    \* @type: <<N, N>> -> Bool;
    vote_msg,
    \* @type: <<N, N>> -> Bool;
    votes,
    \* @type: N -> Bool;
    leader,
    \* @type: Set(N);
    voting_quorum

INSTANCE consensus_wo_decide
===============================================================================
