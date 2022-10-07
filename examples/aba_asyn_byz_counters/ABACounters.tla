------------------------------- MODULE ABACounters --------------------------------
(*
   An encoding of the asynchronous Byzantine consensus protocol in Fig.3 [1]:

   [1] Bracha, Gabriel, and Sam Toueg. "Asynchronous consensus and broadcast protocols."
   Journal of the ACM (JACM) 32.4 (1985): 824-840.

   This a version that uses message counters.

   Jure Kukovec, 2022
 *)

EXTENDS Integers, FiniteSets, Apalache

\* @typeAlias: counter = Int -> Int;
ALIASES == TRUE

CONSTANTS
    \* The number of processes: correct + Byzantine
    \*
    \* @type: Int;
    N,
    \* The upper bound on the number of faulty processes
    \*
    \* @type: Int;
    T,
    \* The actual number of faulty processes
    \*
    \* @type: Int;
    F

\* The set of correct processes
Corr == 1..(N - F)

\* The set of Byzantine processes
Byz == (N - F + 1)..N

\* The set of all processes
Proc == 1..N

VARIABLES
    \* The counter for all sent ECHO messages
    \*
    \* @type: Int;
    sentEcho,
    \* The counter for all sent READY messages
    \*
    \* @type: Int;
    sentReady,
    \* The counter for all received ECHO messages (for each process)
    \*
    \* @type: $counter;
    rcvdEcho,
    \* The counter for all received READY messages for each process
    \*
    \* @type: $counter;
    rcvdReady,
    \* The control state of a process
    \*
    \* @type: Int -> Str;
    pc

InitFrom(InitLocs) ==
    /\ pc \in [ Corr -> InitLocs ]
    /\ rcvdEcho = [ p \in Corr |-> 0 ]
    /\ rcvdReady = [ p \in Corr |-> 0 ]
    \* the Byzantine processes are free to send messages whenever they like
    /\ \E initEcho \in Int:
        /\ sentEcho = initEcho
        /\ 0 <= initEcho 
        /\ initEcho <= F
    /\ \E initReady \in Int:
        /\ sentReady = initReady
        /\ 0 <= initReady 
        /\ initReady <= F

Init ==
    InitFrom({ "V0", "V1" })

Init0 ==
    InitFrom({ "V0" })

Init1 ==
    InitFrom({ "V1" })

Receive(p, nextEcho, nextReady) ==
    /\ rcvdEcho[p] <= nextEcho
    /\ rcvdReady[p] <= nextReady
    /\ rcvdEcho' = [ rcvdEcho EXCEPT ![p] = nextEcho ]
    /\ rcvdReady' = [ rcvdReady EXCEPT ![p] = nextReady ]

SendEcho(p, nextEcho, nextReady) ==
    /\ \/ pc[p] = "V1"
       \/ /\ pc[p] = "V0"
          /\ \/ nextEcho >= (N + T + 2) \div 2
          /\ \/ nextReady >= T + 1
    /\ pc' = [ pc EXCEPT ![p] = "EC" ]
    /\ sentEcho' = sentEcho + 1
    /\ UNCHANGED sentReady

SendReady(p, nextEcho, nextReady) ==
    /\ pc[p] = "EC"
    /\ \/ nextEcho >= (N + T + 2) \div 2
       \/ nextReady >= T + 1
    /\ pc' = [ pc EXCEPT ![p] = "RD" ]
    /\ sentReady' = sentReady + 1
    /\ UNCHANGED sentEcho

Decide(p, nextReady) ==
    /\ pc[p] = "RD"
    /\ nextReady >= 2 * T + 1
    /\ pc' = [ pc EXCEPT ![p] = "AC" ]
    /\ UNCHANGED <<sentEcho, sentReady>>

Next ==
    \E p \in Corr, nextEcho, nextReady \in Int:
        /\ 0 <= nextEcho
        /\ 0 <= nextReady
        /\ nextEcho <= sentEcho
        /\ nextReady <= sentReady
        /\ Receive(p, nextEcho, nextReady)
        /\ \/ SendEcho(p, nextEcho, nextReady)
           \/ SendReady(p, nextEcho, nextReady)
           \/ Decide(p, nextReady)
           \/ UNCHANGED <<pc, sentEcho, sentReady>>

NoDecide ==
    \A p \in Corr:
        pc[p] /= "AC"

===============================================================================
