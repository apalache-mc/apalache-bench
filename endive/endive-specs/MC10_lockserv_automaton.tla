----------------- MODULE MC10_lockserv_automaton -------------------------------
Node == { "1_OF_N", "2_OF_N", "3_OF_N", "4_OF_N", "5_OF_N", "6_OF_N", "7_OF_N", "8_OF_N", "9_OF_N", "10_OF_N" }

VARIABLE
    \* @type: N -> Bool;
    lock_msg,
    \* @type: N -> Bool;
    grant_msg,
    \* @type: N -> Bool;
    unlock_msg,
    \* @type: N -> Bool;
    holds_lock,
    \* @type: Bool;
    held

INSTANCE lockserv_automaton
===============================================================================
