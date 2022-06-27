--------------------- MODULE MC20_TRUE_TRUE -----------------------

RM == {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20}
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
