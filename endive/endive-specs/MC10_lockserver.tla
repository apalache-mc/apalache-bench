-------------------- MODULE MC10_lockserver ---------------------------------
Server == { "1_OF_S", "2_OF_S", "3_OF_S", "4_OF_S", "5_OF_S", "6_OF_S", "7_OF_S", "8_OF_S", "9_OF_S", "10_OF_S" }
Client == { "1_OF_C", "2_OF_C", "3_OF_C", "4_OF_C", "5_OF_C", "6_OF_C", "7_OF_C", "8_OF_C", "9_OF_C", "10_OF_C" }
Nil == ""

VARIABLE
    \* @type: S -> Bool;
    semaphore,
    \* @type: C -> Set(S);
    clientlocks

INSTANCE lockserver
===============================================================================
