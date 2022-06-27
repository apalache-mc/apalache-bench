--------------------- MODULE MC10_FALSE_FALSE -----------------------

RM == {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
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
