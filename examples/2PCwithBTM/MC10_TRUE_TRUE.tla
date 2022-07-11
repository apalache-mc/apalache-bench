--------------------- MODULE MC10_TRUE_TRUE -----------------------

RM == {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
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
