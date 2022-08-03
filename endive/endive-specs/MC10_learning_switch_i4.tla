-------------------- MODULE MC10_learning_switch_i4 ----------------------------
Packet == { "1_OF_P", "2_OF_P", "3_OF_P", "4_OF_P", "5_OF_P", "6_OF_P", "7_OF_P", "8_OF_P", "9_OF_P" }
Node == { "1_OF_N", "2_OF_N", "3_OF_N", "4_OF_N", "5_OF_N", "6_OF_N", "7_OF_N", "8_OF_N", "9_OF_N", "10_OF_N" }

VARIABLE
    \* @type: Set(<<P, N, N>>);
    pending,
    \* @type: P -> N;
    src,
    \* @type: P -> N;
    dst,
    \* @type: N -> N;
    link,
    \* @type: Set(<<N, N>>);
    route_dom,
    \* @type: Set(<<N, N, N>>);
    route_tc

INSTANCE learning_switch_i4
===============================================================================
