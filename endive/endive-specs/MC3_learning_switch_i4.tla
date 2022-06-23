-------------------- MODULE MC3_learning_switch_i4 ----------------------------
Packet == { "1_OF_P", "2_OF_P" }
Node == { "1_OF_N", "2_OF_N", "3_OF_N" }

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
