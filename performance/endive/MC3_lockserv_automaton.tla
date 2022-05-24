----------------- MODULE MC3_lockserv_automaton -------------------------------
Node == { "1_OF_N", "2_OF_N", "3_OF_N" }

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
