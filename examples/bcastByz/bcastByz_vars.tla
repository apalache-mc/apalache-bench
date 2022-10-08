------------------------- MODULE bcastByz_vars ---------------------------------

VARIABLE
  \* @type: Int -> Str;
  pc             (* the control state of each process *)
VARIABLE
  \* @type: Int -> Int;
  rcvd           (* the # of messages received by each process *)
VARIABLE
  \* @type: Int;
  sent           (* the # of messages sent by all correct processes *)

===============================================================================
