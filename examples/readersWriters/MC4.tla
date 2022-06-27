---- MODULE MC4 ----

NumActors == 4

VARIABLES
    \* @type: Set(Int);
    readers, \* set of processes currently reading
    \* @type: Set(Int);
    writers, \* set of processes currently writing
    \* @type: Seq(<<Str, Int>>);
    waiting  \* queue of processes waiting to access the resource

INSTANCE ReadersWriters

===================
