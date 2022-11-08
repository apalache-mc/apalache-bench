------------------------------ MODULE cf1s_folklore ------------------------------

(* An encoding of the consensus algorithm with Byzantine faults in one communication step [1]. Here 
   we consider only the algorithm itself (Algorithm 2, lines 1--4), without looking at the underlying 
   consensus algorithm. 
   
   [1] Dobre, Dan, and Neeraj Suri. "One-step consensus with zero-degradation." Dependable Systems and 
   Networks, 2006. DSN 2006. International Conference on. IEEE, 2006.
  
   This file is a subject to the license that is bundled together with this package and can be found 
   in the file LICENSE.
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

VARIABLES 
  \* @type: Int;
  nSnt0,    
  \* @type: Int;
  nSnt1,
  \* @type: Int;
  nSnt0F,   
  \* @type: Int;
  nSnt1F,  
  \* @type: Int;
  nFaulty,  
  \* @type: Int -> Str;
  pc,       
  \* @type: Int -> Int;
  nRcvd0,   
  \* @type: Int -> Int;
  nRcvd1


Proc == 1 .. N
Status == { "V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1", "BYZ" }
vars == << nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, pc, nRcvd0, nRcvd1 >>


Init ==
  /\ pc \in [ Proc -> { "V0", "V1" } ]
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nSnt0F = 0
  /\ nSnt1F = 0
  /\ nFaulty = 0
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]
  
Faulty(i) ==
  /\ nFaulty < F
  /\ pc[i] # "BYZ"
  /\ pc' = [ pc EXCEPT ![i] = "BYZ" ] 
  /\ nFaulty' = nFaulty + 1  
  /\ nSnt0F' = nSnt0F + IF pc[i] = "V0" THEN 1 ELSE 0
  /\ nSnt1F' = nSnt1F + IF pc[i] = "V1" THEN 1 ELSE 0
  /\ UNCHANGED << nSnt0, nSnt1, nRcvd0, nRcvd1 >>
  
Propose(i) ==
  \/ /\ pc[i] = "V0"
     /\ pc' = [ pc EXCEPT ![i] = "S0" ]
     /\ nSnt0' = nSnt0 + 1
     /\ UNCHANGED << nSnt1, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>
  \/ /\ pc[i] = "V1"
     /\ pc' = [ pc EXCEPT ![i] = "S1" ]
     /\ nSnt1' = nSnt1 + 1
     /\ UNCHANGED << nSnt0, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>
     
Receive(i) ==
  \/ /\ \E k \in Int:
      /\ nRcvd0[i] < k
      /\ k <= nSnt0 + nSnt0F
      /\ nRcvd0' = [ nRcvd0 EXCEPT ![i] = k ]
     /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nFaulty, pc, nSnt1F, nRcvd1 >>     
  \/ /\ \E k \in Int:
      /\ nRcvd1[i] < k
      /\ k <= nSnt1 + nSnt1F
      /\ nRcvd1' = [ nRcvd1 EXCEPT ![i] = k ]
     /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nFaulty, pc, nSnt1F, nRcvd0 >>    
     
Decide(i) ==
  /\ \/ pc[i] = "S0"
     \/ pc[i] = "S1"
  /\ nRcvd0[i] + nRcvd1[i] >= N - T
  /\ \/ /\ nRcvd0[i] >= N - T
        /\ pc' = [ pc EXCEPT ![i] = "D0" ]      
     \/ /\ nRcvd1[i] >= N - T
        /\ pc' = [ pc EXCEPT ![i] = "D1" ]
     \/ /\ nRcvd0[i] < N - T
        /\ nRcvd1[i] < N - T
        /\ pc[i] \in {"S0", "S1"}
        /\ pc' = [ pc EXCEPT ![i] = IF pc[i] = "S0" THEN "U0" ELSE "U1" ]
  /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>

Next ==
  \E self \in Proc : 
    \/ Receive(self) 
    \/ Propose(self) 
    \/ Decide(self) 
    \/ Faulty(self)
    \/ UNCHANGED vars                  

(* All processes propose 0. *)
Init0 ==
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nSnt0F = 0
  /\ nSnt1F = 0
  /\ nFaulty = 0
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]
  (* /\ nStep = 0 *)
  
(* All processes propose 1. *)  
Init1 ==
  /\ pc = [ i \in Proc |-> "V1" ]
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nSnt0F = 0
  /\ nSnt1F = 0
  /\ nFaulty = 0
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]  


TypeOK == 
  /\ pc \in [ Proc -> Status ]          
  /\ nSnt0 \in 0..N
  /\ nSnt1 \in 0..N
  /\ nSnt0F \in 0..N
  /\ nSnt1F \in 0..N
  /\ nFaulty \in 0..T
  /\ nRcvd0 \in [ Proc -> 0..N ]
  /\ nRcvd1 \in [ Proc -> 0..N ]
  
 (* If all processes propose 0, then every process crashes or decides 0. *) 
OneStep0_Ltl ==
  (\A i \in Proc : pc[i] = "V0") => 
  [](\A i \in Proc : pc[i] # "U0" /\ pc[i] # "U1" /\ pc[i] # "D1")

(* If all processes propose 1, then every process crashes or decides 1. *)
OneStep1_Ltl ==  
  (\A i \in Proc : pc[i] = "V1") => <>(\A i \in Proc : pc[i] # "U0" /\ pc[i] # "U1" /\ pc[i] # "D0")
  
OneStep0 == \A i \in Proc : pc[i] # "U0" /\ pc[i] # "U1"

=============================================================================
