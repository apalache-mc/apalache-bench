--------------- MODULE MC10_majorityset_leader_election ---------------------
Node == { "1_OF_N", "2_OF_N", "3_OF_N", "4_OF_N", "5_OF_N", "6_OF_N", "7_OF_N", "8_OF_N", "9_OF_N", "10_OF_N" }

VARIABLES
    \* @type: N -> Set(N);
    vote,
    \* @type: Set(N);
    leader,
    \* @type: N -> Set(N);
    voters

INSTANCE majorityset_leader_election
===============================================================================
