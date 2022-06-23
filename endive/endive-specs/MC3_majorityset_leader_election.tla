--------------- MODULE MC3_majorityset_leader_election ---------------------
Node == { "1_OF_N", "2_OF_N", "3_OF_N" }

VARIABLES
    \* @type: N -> Set(N);
    vote,
    \* @type: Set(N);
    leader,
    \* @type: N -> Set(N);
    voters

INSTANCE majorityset_leader_election
===============================================================================
