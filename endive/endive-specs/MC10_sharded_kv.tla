-------------------- MODULE MC10_sharded_kv -----------------------------
Value   == { "1_OF_V", "2_OF_V", "3_OF_V", "4_OF_V", "5_OF_V", "6_OF_V", "7_OF_V", "8_OF_V", "9_OF_V", "10_OF_V" }
Key     == { "1_OF_K", "2_OF_K", "3_OF_K", "4_OF_K", "5_OF_K", "6_OF_K", "7_OF_K", "8_OF_K", "9_OF_K", "10_OF_K" }
Node    == { "1_OF_N", "2_OF_N", "3_OF_N", "4_OF_N", "5_OF_N", "6_OF_N", "7_OF_N", "8_OF_N", "9_OF_N", "10_OF_N" }

Nil == "Nil_OF_V"

VARIABLES
    \* @type: N -> (K -> V);
    table,
    \* @type: N -> Set(K);
    owner,
    \* @type: Set(<<N, K, V>>);
    transfer_msg

INSTANCE sharded_kv
================================================================================
