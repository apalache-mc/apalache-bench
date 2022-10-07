------------------------------ MODULE bcastByz ------------------------------

(* Modification of bcastByz using counters.
  
   Jure Kukovec, 2022
  
   This file is a subject to the license that is bundled together with this package 
   and can be found in the file LICENSE.
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
Faulty == (N - F + 1)..N

VARIABLE 
  \* @type: Int -> Str;
  pc             (* the control state of each process *)
VARIABLE 
  \* @type: Int -> Int;
  rcvd           (* the # of messages received by each process *)
VARIABLE 
  \* @type: Int;
  sent           (* the # of messages sent by all correct processes *)

Proc == 1 .. N             
vars == << pc, rcvd, sent>>


Init == 
  /\ sent = 0                          (* No messages sent initially *)
  /\ pc \in [ Proc -> {"V0", "V1"} ]    (* Some processes received INIT messages, some didn't *)
  /\ rcvd = [ i \in Proc |-> 0 ]       (* No messages received initially *)
        
InitNoBcast == 
  /\ sent = 0
  /\ pc = [ p \in Proc |-> "V0" ] 
  /\ rcvd = [ i \in Proc |-> 0 ]

ReceiveFromAnySender(self) ==
  \E newMessagesCtr \in Int:
    /\ 0 <= newMessagesCtr
    /\ newMessagesCtr <= sent + F
    /\ rcvd' = [rcvd EXCEPT ![self] = newMessagesCtr]

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent + 1
       
UponNonFaulty(self) ==
  /\ pc[self] \in { "V0", "V1" }
  /\ \E newRcvd \in Int:
    /\ rcvd' = [rcvd EXCEPT ![self] = newRcvd]
    /\ newRcvd >= N - 2*T
    /\ newRcvd < N - T
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent + 1
        
UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in { "V0", "V1" }
  /\ \E newRcvd \in Int:
    /\ rcvd' = [rcvd EXCEPT ![self] = newRcvd]
    /\ newRcvd >= N - 2*T
    /\ newRcvd <= N 
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent + 1
        
UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ \E newRcvd \in Int:
    /\ rcvd' = [rcvd EXCEPT ![self] = newRcvd]
    /\ newRcvd >= N - T
    /\ newRcvd <= N 
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ UNCHANGED sent

Step(self) == 
  /\ ReceiveFromAnySender(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

Next ==
     \/ \E self \in Corr: Step(self)                     
     \/ UNCHANGED vars (* add a self-loop for terminating computations *)

Spec == Init /\ [][Next]_vars 

SpecNoBcast == InitNoBcast /\ [][Next]_vars

TypeOK == 
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]          
  /\ sent \in 0..N
  /\ rcvd \in [ Proc -> 0..N ]
          
(****************************** SPECIFICATION ******************************)

(* If a correct process broadcasts, then every correct process eventually accepts. *)
CorrLtl == (\A i \in Corr: pc[i] = "V1") => <>(\A i \in Corr: pc[i] = "AC")

(* If a correct process accepts, then every correct process accepts. *)
RelayLtl == []((\E i \in Corr: pc[i] = "AC") => <>(\A i \in Corr: pc[i] = "AC"))

(* If no correct process don't broadcast ECHO messages then no correct processes accept. *)  
UnforgLtl == (\A i \in Corr: pc[i] = "V0") => [](\A i \in Corr: pc[i] /= "AC")

(* The special case of the unforgeability property. When our algorithms start with InitNoBcast,
   we can rewrite UnforgLtl as a first-order formula.     
 *)          
Unforg == (\A i \in Proc: i \in Corr => (pc[i] /= "AC")) 
            
IndInv_Unforg_NoBcast ==  
  /\ TypeOK
  /\ sent = 0
  /\ pc = [ i \in Proc |-> "V0" ]

IndInv_Unforg_NoBcast_TLC ==  
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ \A i \in Proc : pc[i] /= "AC"
  /\ sent = 0  
  /\ rcvd \in [ Proc -> 0..N ]   
        
=============================================================================
