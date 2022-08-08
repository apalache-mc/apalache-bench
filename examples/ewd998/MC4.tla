---- MODULE MC4 ----
N == 4

VARIABLES
 \* @type: Int -> Bool;
 active,     \* activation status of nodes
 \* @type: Int -> Str;
 color,      \* color of nodes
 \* @type: Int -> Int;
 counter,    \* nb of sent messages - nb of rcvd messages per node
 \* @type: Int -> Int;
 pending,    \* nb of messages in transit to node
 \* @type: [ pos: Int, q: Int, color: Str ];
 token       \* token structure

INSTANCE EWD998

====
