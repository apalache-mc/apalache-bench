--------------------- MODULE MC4 -----------------------
EXTENDS Sequences

N == 4
\* @type: Seq(Int);
Id == <<3, 2, 1, 4>>

VARIABLES
    \* @type: Int -> Set(Int);
    msgs,
    \* @type: Int -> Str;
    pc,
    \* @type: Int -> Bool;
    initiator,
    \* @type: Int -> Str;
    state

INSTANCE ChangRoberts
=========================================================
