------------------------------- MODULE ABASets --------------------------------
(*
   An encoding of the asynchronous Byzantine consensus protocol in Fig.3 [1]:

   [1] Bracha, Gabriel, and Sam Toueg. "Asynchronous consensus and broadcast protocols."
   Journal of the ACM (JACM) 32.4 (1985): 824-840.

   This a version that uses message sets instead of message counters.

   Igor Konnov, 2022
 *)

EXTENDS Integers, FiniteSets

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
    \* The set of all sent ECHO messages (the process ids)
    \*
    \* @type: Set(Int);
    sentEcho,
    \* The set of all sent READY messages (the process ids)
    \*
    \* @type: Set(Int);
    sentReady,
    \* The set of all received ECHO messages (the process ids)
    \*
    \* @type: Int -> Set(Int);
    rcvdEcho,
    \* The set of all received READY messages (the process ids)
    \*
    \* @type: Int -> Set(Int);
    rcvdReady,
    \* The control state of a process
    \*
    \* @type: Int -> Str;
    pc

InitFrom(InitLocs) ==
    /\ pc \in [ Corr -> InitLocs ]
    /\ rcvdEcho = [ p \in Corr |-> {} ]
    /\ rcvdReady = [ p \in Corr |-> {} ]
    \* the Byzantine processes are free to send messages whenever they like
    /\ sentEcho \in SUBSET Byz
    /\ sentReady \in SUBSET Byz

Init ==
    InitFrom({ "V0", "V1" })

Init0 ==
    InitFrom({ "V0" })

Init1 ==
    InitFrom({ "V1" })

Receive(p, nextEcho, nextReady) ==
    /\ rcvdEcho[p] \subseteq nextEcho
    /\ rcvdReady[p] \subseteq nextReady
    /\ rcvdEcho' = [ rcvdEcho EXCEPT ![p] = nextEcho ]
    /\ rcvdReady' = [ rcvdReady EXCEPT ![p] = nextReady ]

SendEcho(p, nextEcho, nextReady) ==
    /\ \/ pc[p] = "V1"
       \/ /\ pc[p] = "V0"
          /\ \/ Cardinality(nextEcho) >= (N + T + 2) \div 2
          /\ \/ Cardinality(nextReady) >= T + 1
    /\ pc' = [ pc EXCEPT ![p] = "EC" ]
    /\ sentEcho' = sentEcho \union { p }
    /\ UNCHANGED sentReady

SendReady(p, nextEcho, nextReady) ==
    /\ pc[p] = "EC"
    /\ \/ Cardinality(nextEcho) >= (N + T + 2) \div 2
       \/ Cardinality(nextReady) >= T + 1
    /\ pc' = [ pc EXCEPT ![p] = "RD" ]
    /\ sentReady' = sentReady \union { p }
    /\ UNCHANGED sentEcho

Decide(p, nextReady) ==
    /\ pc[p] = "RD"
    /\ Cardinality(nextReady) >= 2 * T + 1
    /\ pc' = [ pc EXCEPT ![p] = "AC" ]
    /\ UNCHANGED <<sentEcho, sentReady>>

Next ==
    \E p \in Corr, nextEcho \in SUBSET sentEcho, nextReady \in SUBSET sentReady:
        /\ Receive(p, nextEcho, nextReady)
        /\ \/ SendEcho(p, nextEcho, nextReady)
           \/ SendReady(p, nextEcho, nextReady)
           \/ Decide(p, nextReady)
           \/ UNCHANGED <<pc, sentEcho, sentReady>>

NoDecide ==
    \A p \in Corr:
        pc[p] /= "AC"

===============================================================================
