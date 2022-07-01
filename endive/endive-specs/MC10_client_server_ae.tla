--------------------- MODULE MC10_client_server_ae -----------------------------
Node == { "1_OF_N", "2_OF_N", "3_OF_N", "4_OF_N", "5_OF_N", "6_OF_N", "7_OF_N", "8_OF_N", "9_OF_N", "10_OF_N" }
Request == { "1_OF_Q", "2_OF_Q", "3_OF_Q", "4_OF_Q", "5_OF_Q", "6_OF_Q", "7_OF_Q", "8_OF_Q", "9_OF_Q" }
Response == { "1_OF_A", "2_OF_A", "3_OF_A", "4_OF_A", "5_OF_A", "6_OF_A", "7_OF_A", "8_OF_A", "9_OF_A" }

VARIABLES
    \* @type: Set(<<Q, A>>);
    match,
    \* @type: Set(<<N, Q>>);
    request_sent,
    \* @type: Set(<<N, A>>);
    response_sent,
    \* @type: Set(<<N, A>>);
    response_received

INSTANCE client_server_ae

===============================================================================
