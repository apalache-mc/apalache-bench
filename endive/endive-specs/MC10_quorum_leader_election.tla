-------------- MODULE MC10_quorum_leader_election -----------------------------
Node == { "1_OF_N", "2_OF_N", "3_OF_N", "4_OF_N", "5_OF_N", "6_OF_N", "7_OF_N", "8_OF_N", "9_OF_N", "10_OF_N" }
Nil == "Nil_OF_N"

VARIABLES
    \* @type: N -> Bool;
    isleader,
    \* @type: N -> N;
    voted

INSTANCE quorum_leader_election
===============================================================================
