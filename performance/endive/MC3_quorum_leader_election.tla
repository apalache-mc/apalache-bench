-------------- MODULE MC3_quorum_leader_election -----------------------------
Node == { "1_OF_N", "2_OF_N", "3_OF_N" }
Nil == "Nil_OF_N"

VARIABLES
    \* @type: N -> Bool;
    isleader,
    \* @type: N -> N;
    voted

INSTANCE quorum_leader_election
===============================================================================
