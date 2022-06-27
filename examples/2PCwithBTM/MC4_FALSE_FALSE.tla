--------------------- MODULE MC4_FALSE_FALSE -----------------------

RM == {1, 2, 3, 4}
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
