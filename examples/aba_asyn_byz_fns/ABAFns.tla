------------------------------- MODULE ABAFns --------------------------------
(*
   An encoding of the asynchronous Byzantine consensus protocol in Fig.3 [1]:

   [1] Bracha, Gabriel, and Sam Toueg. "Asynchronous consensus and broadcast protocols."
   Journal of the ACM (JACM) 32.4 (1985): 824-840.

   This a version that uses message counters.

   Jure Kukovec, 2022
 *)

EXTENDS Integers, FiniteSets, Apalache

\* @typeAlias: charFn = Int -> Bool;
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
    \* The characteristic function of the set of all sent ECHO messages (the process ids)
    \*
    \* @type: $charFn;
    sentEcho,
    \* The characteristic function of the set of all sent READY messages (the process ids)
    \*
    \* @type: $charFn;
    sentReady,
    \* The characteristic function of the set of all received ECHO messages (the process ids)
    \* for each process
    \*
    \* @type: Int -> $charFn;
    rcvdEcho,
    \* The characteristic function of the set of all received READY messages (the process ids)
    \* for each process
    \*
    \* @type: Int -> $charFn;
    rcvdReady,
    \* The control state of a process
    \*
    \* @type: Int -> Str;
    pc

EmptySetFn == [p \in Proc |-> FALSE]

InitFrom(InitLocs) ==
    /\ pc \in [ Corr -> InitLocs ]
    /\ rcvdEcho = [ p \in Corr |-> EmptySetFn ]
    /\ rcvdReady = [ p \in Corr |-> EmptySetFn ]
    \* the Byzantine processes are free to send messages whenever they like
    /\ sentEcho \in [Proc -> BOOLEAN]
    /\ \A p \in Corr: sentEcho[p] = FALSE
    /\ sentReady \in [Proc -> BOOLEAN]
    /\ \A p \in Corr: sentReady[p] = FALSE

Init ==
    InitFrom({ "V0", "V1" })

Init0 ==
    InitFrom({ "V0" })

Init1 ==
    InitFrom({ "V1" })

\* @type: ($charFn, $charFn) => Bool;
FnSubseteq(lhs, rhs) ==
    \* Assumption: DOMAIN lhs \subseteq DOMAIN rhs
    \A p \in DOMAIN lhs: lhs[p] => rhs[p]

Receive(p, nextEcho, nextReady) ==
    /\ FnSubseteq(rcvdEcho[p], nextEcho)
    /\ FnSubseteq(rcvdReady[p], nextReady)
    /\ rcvdEcho' = [ rcvdEcho EXCEPT ![p] = nextEcho ]
    /\ rcvdReady' = [ rcvdReady EXCEPT ![p] = nextReady ]

\* @type: ($charFn) => Int;
FnCardinality(f) ==
    LET
        \* @type: (Int, Int) => Int; 
        plusTrue(a,b) == a + IF f[b] THEN 1 ELSE 0 
    IN ApaFoldSet(plusTrue, 0, DOMAIN f)

SendEcho(p, nextEcho, nextReady) ==
    /\ \/ pc[p] = "V1"
       \/ /\ pc[p] = "V0"
          /\ \/ FnCardinality(nextEcho) >= (N + T + 2) \div 2
          /\ \/ FnCardinality(nextReady) >= T + 1
    /\ pc' = [ pc EXCEPT ![p] = "EC" ]
    /\ sentEcho' = [sentEcho EXCEPT ![p] = TRUE]
    /\ UNCHANGED sentReady

SendReady(p, nextEcho, nextReady) ==
    /\ pc[p] = "EC"
    /\ \/ FnCardinality(nextEcho) >= (N + T + 2) \div 2
       \/ FnCardinality(nextReady) >= T + 1
    /\ pc' = [ pc EXCEPT ![p] = "RD" ]
    /\ sentReady' = [sentReady EXCEPT ![p] = TRUE]
    /\ UNCHANGED sentEcho

Decide(p, nextReady) ==
    /\ pc[p] = "RD"
    /\ FnCardinality(nextReady) >= 2 * T + 1
    /\ pc' = [ pc EXCEPT ![p] = "AC" ]
    /\ UNCHANGED <<sentEcho, sentReady>>

SentFnSet == [Byz -> BOOLEAN]

Next ==
    \E p \in Corr, nextEcho \in SentFnSet, nextReady \in SentFnSet:
        /\ FnSubseteq(nextEcho, sentEcho)
        /\ FnSubseteq(nextReady, sentReady)
        /\ Receive(p, nextEcho, nextReady)
        /\ \/ SendEcho(p, nextEcho, nextReady)
           \/ SendReady(p, nextEcho, nextReady)
           \/ Decide(p, nextReady)
           \/ UNCHANGED <<pc, sentEcho, sentReady>>

NoDecide ==
    \A p \in Corr:
        pc[p] /= "AC"

===============================================================================
