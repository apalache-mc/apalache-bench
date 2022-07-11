--------------------- MODULE MC20_FALSE_FALSE -----------------------

RM == {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20}
RMMAYFAIL == FALSE
TMMAYFAIL ==  FALSE

VARIABLES
    \* @type: Int -> Str;
    rmState,
    \* @type: Str;
    tmState,
    \* @type: Int -> Str;
    pc

INSTANCE 2PCwithBTM
=========================================================
