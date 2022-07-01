------------------- MODULE MC10_two_phase_commit -----------------------------
Node == { "1_OF_N", "2_OF_N", "3_OF_N", "4_OF_N", "5_OF_N", "6_OF_N", "7_OF_N", "8_OF_N", "9_OF_N", "10_OF_N" }

VARIABLES
    \* @type: Set(N);
    vote_yes,
    \* @type: Set(N);
    vote_no,
    \* @type: Set(N);
    alive,
    \* @type: Set(N);
    go_commit,
    \* @type: Set(N);
    go_abort,
    \* @type: Set(N);
    decide_commit,
    \* @type: Set(N);
    decide_abort,
    \* @type: Bool;
    abort_flag

INSTANCE two_phase_commit
================================================================================
