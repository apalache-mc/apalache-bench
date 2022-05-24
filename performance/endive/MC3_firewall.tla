------------------------ MODULE MC3_firewall -----------------------------
Node == { "1_OF_N", "2_OF_N", "3_OF_N" }

VARIABLE
    \* @type: N -> Bool;
    internal,
    \* @type: N -> Set(N);
    sent,
    \* @type: Set(N);
    allowed_in

INSTANCE firewall
===============================================================================
