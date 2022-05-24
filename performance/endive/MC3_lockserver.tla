-------------------- MODULE MC3_lockserver ---------------------------------
Server == { "1_OF_S", "2_OF_S", "3_OF_S" }
Client == { "1_OF_C", "2_OF_C", "3_OF_C" }
Nil == ""

VARIABLE
    \* @type: S -> Bool;
    semaphore,
    \* @type: C -> Set(S);
    clientlocks

INSTANCE lockserver
===============================================================================
