--------------------- MODULE MC16 -----------------------

N == 16
T == 5
F == 5

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