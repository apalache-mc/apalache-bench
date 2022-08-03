--------------- MODULE MC10_simple_decentralized_lock --------------------------
Node    == { "1_OF_N", "2_OF_N", "3_OF_N", "4_OF_N", "5_OF_N", "6_OF_N", "7_OF_N", "8_OF_N", "9_OF_N", "10_OF_N" }

VARIABLES
    \* @type: Set(<<N, N>>);
    message,
    \* @type: Set(N);
    has_lock

INSTANCE simple_decentralized_lock
================================================================================
