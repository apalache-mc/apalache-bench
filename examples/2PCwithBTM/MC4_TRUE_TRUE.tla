--------------------- MODULE MC4_TRUE_TRUE -----------------------

RM == {1, 2, 3, 4}
RMMAYFAIL == TRUE
TMMAYFAIL ==  TRUE

VARIABLES
    \* @type: Int -> Str;
    rmState,
    \* @type: Str;
    tmState,
    \* @type: Int -> Str;
    pc

INSTANCE 2PCwithBTM
=========================================================
