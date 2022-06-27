--------------------- MODULE MC10 -----------------------
EXTENDS Sequences

N == 10
\* @type: Seq(Int);
Id == <<1, 2, 3, 4, 5, 6, 7, 8, 9, 10>>

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
