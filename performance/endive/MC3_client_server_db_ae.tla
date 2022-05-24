------------------ MODULE MC3_client_server_db_ae -----------------------------
Node == { "1_OF_N", "2_OF_N", "3_OF_N" }
Request == { "1_OF_Q", "2_OF_Q" }
Response == { "1_OF_A", "2_OF_A" }
DbRequestId == { "1_OF_D", "2_OF_D" }

VARIABLES
    \* @type: Set(<<Q, A>>);
    match,
    \* @type: Set(<<N, Q>>);
    request_sent,
    \* @type: Set(<<N, A>>);
    response_sent,
    \* @type: Set(<<N, A>>);
    response_received,
    \* @type: Set(<<D, Q>>);
    db_request_sent,
    \* @type: Set(<<D, A>>);
    db_response_sent,
    \* @type: Set(<<D, N>>);
    t

INSTANCE client_server_db_ae

===============================================================================
