--------------------- MODULE MC19 -----------------------

N == 19
T == 6
F == 6

VARIABLES
    \* @type: Int;
    nSntE,    (* the number of ECHO, READY messages which are sent     *)
    \* @type: Int;
    nSntR,
    \* @type: Int -> Int;
    nRcvdE,   (* the number of ECHO, READY messages which are received *)
    \* @type: Int -> Int;
    nRcvdR,
    \* @type: Int;
    nByz,     (* the number of Byzantine processes                     *)
    \* @type: Int -> Str;
    pc        (* program counters *)

INSTANCE aba_asyn_byz
=========================================================