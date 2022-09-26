--------------------- MODULE MC7 -----------------------

N == 7
T == 2
F == 2

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