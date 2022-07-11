--------------- MODULE MC3_sharded_kv_no_lost_keys -----------------------------
Value   == { "1_OF_V", "2_OF_V", "3_OF_V" }
Key     == { "1_OF_K", "2_OF_K", "3_OF_K" }
Node    == { "1_OF_N", "2_OF_N", "3_OF_N" }

Nil == "Nil_OF_V"

VARIABLES
    \* @type: N -> (K -> V);
    table,
    \* @type: N -> Set(K);
    owner,
    \* @type: Set(<<N, K, V>>);
    transfer_msg

INSTANCE sharded_kv_no_lost_keys
================================================================================
