---- MODULE MC20 ----

NumActors == 20

VARIABLES
    \* @type: Set(Int);
    readers, \* set of processes currently reading
    \* @type: Set(Int);
    writers, \* set of processes currently writing
    \* @type: Seq(<<Str, Int>>);
    waiting  \* queue of processes waiting to access the resource

INSTANCE ReadersWriters

===================
