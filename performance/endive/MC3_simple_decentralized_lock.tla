--------------- MODULE MC3_simple_decentralized_lock --------------------------
Node    == { "1_OF_N", "2_OF_N", "3_OF_N" }

VARIABLES
    \* @type: Set(<<N, N>>);
    message,
    \* @type: Set(N);
    has_lock

INSTANCE simple_decentralized_lock
================================================================================
