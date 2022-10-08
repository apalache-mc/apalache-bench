------------------------------ MODULE nbacg_guer01 ------------------------------

(* An encoding of a parameterized model of the asynchronous non-blocking atomic commitment 
   algorithm with failure detectors in TLA+. The algorithm is described in the following paper:
 
   [1] Guerraoui, Rachid. "On the hardness of failure-sensitive agreement problems." Information 
   Processing Letters 79.2 (2001): 99-104.
 
   Jure Kukovec, 2022
 
   This file is a subject to the license that is bundled together with this package and can 
   be found in the file LICENSE.
 *)


EXTENDS Integers, FiniteSets

CONSTANTS 
  \* @type: Int;
  N

VARIABLES 
  \* @type: Int;
  nSntNo,     
  \* @type: Int;
  nSntYes,   
  \* @type: Int;
  nSntNoF,   
  \* @type: Int;
  nSntYesF,  
  \* @type: Int -> Int;
  nRcvdYes,  
  \* @type: Int -> Int;
  nRcvdNo,   
  \* @type: Int -> Bool;
  someFail,  
  \* @type: Int -> Str;
  pc
                          

Proc == 1 .. N
Status == { "YES", "NO", "SENT", "ABORT", "COMMIT", "BYZ" }
vars == << nSntNo, nSntYes, nSntYesF, nSntNoF, nRcvdNo, nRcvdYes, someFail, pc >>



Init ==  
  /\ nSntNo = 0                         
  /\ nSntYes = 0
  /\ nSntNoF = 0 
  /\ nSntYesF = 0    
  /\ nRcvdYes = [ i \in Proc |-> 0 ]
  /\ nRcvdNo = [ i \in Proc |-> 0 ]  
  /\ pc \in [ Proc -> { "NO", "YES" } ] 
  /\ someFail \in [ Proc -> BOOLEAN ]   
  
InitYes ==  
  /\ nSntNo = 0                        
  /\ nSntYes = 0
  /\ nSntNoF = 0
  /\ nSntYesF = 0    
  /\ nRcvdYes = [ i \in Proc |-> 0 ]    
  /\ nRcvdNo = [ i \in Proc |-> 0 ]  
  /\ pc \in [ Proc -> { "YES" } ]       
  /\ someFail \in [ Proc -> BOOLEAN ]   
  
InitNo ==  
  /\ nSntNo = 0                         
  /\ nSntYes = 0
  /\ nSntNoF = 0
  /\ nSntYesF = 0    
  /\ nRcvdYes = [ i \in Proc |-> 0 ]
  /\ nRcvdNo = [ i \in Proc |-> 0 ]  
  /\ pc \in [ Proc -> { "NO" } ]        
  /\ someFail \in [ Proc -> BOOLEAN ]   
  
(* Some process will crash in the next state. If the process has not proposed its initial 
   value, the upper bound of the number of messages with the same value will be increased. 
 *)  
Crash(i) ==
  /\ pc[i] # "BYZ"                      
  /\ pc' = [ pc EXCEPT ![i] = "BYZ" ]
  /\ nSntYesF' = nSntYesF + IF pc[i] = "YES" THEN 1 ELSE 0
  /\ nSntNoF' = nSntNoF + IF pc[i] = "No" THEN 1 ELSE 0
  /\ UNCHANGED << nSntNo, nSntYes, nRcvdNo, nRcvdYes, someFail >>

(* A process starts receiving messages after sending its vote. If a process crashed or decides, 
   it stops receiving messages. 
 *)    
Receive(i) ==
  \/ /\ pc[i] = "SENT"
     /\ nRcvdYes[i] < nSntYes + nSntYesF    (* receives a YES message *)                       
     /\ nRcvdYes' = [ nRcvdYes EXCEPT ![i] = nRcvdYes[i] + 1 ]
     /\ UNCHANGED << nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdNo, someFail, pc >>     
  \/ /\ pc[i] = "SENT"
     /\ nRcvdNo[i] < nSntNo + nSntNoF       (* receives a NO message *)
     /\ nRcvdNo' = [ nRcvdNo EXCEPT ![i] = nRcvdNo[i] + 1 ]
     /\ UNCHANGED << nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, someFail, pc >>  
  \/ /\ pc[i] = "SENT"
     /\ nRcvdYes[i] =  nSntYes + nSntYesF     (* all messages are received *) 
     /\ nRcvdNo[i] = nSntNo + nSntNoF  
     /\ UNCHANGED vars                       (* this conditions is added to avoid deadlocks *)       

(* A correct process sends YES messages to all processes. *)
SendYes(i) ==
  /\ pc[i] = "YES"    
  /\ someFail[i] = FALSE
  /\ pc' = [ pc EXCEPT ![i] = "SENT" ]
  /\ nSntYes' = nSntYes + 1
  /\ UNCHANGED << nSntNo, nSntYesF, nSntNoF, nRcvdNo, nRcvdYes, someFail >>
  
(* A correct process sends NO messages to all processes. *)  
SendNo(i) ==
  /\ pc[i] = "NO"   
  /\ someFail[i] = FALSE 
  /\ pc' = [ pc EXCEPT ![i] = "SENT" ]
  /\ nSntNo' = nSntNo + 1
  /\ UNCHANGED << nSntYes, nSntYesF, nSntNoF, nRcvdNo, nRcvdYes, someFail >>  
  
(* A suspicious process aborts. *)
AbortNoYes(i) ==
  /\ someFail[i] = TRUE
  /\ \/ pc[i] = "YES"
     \/ pc[i] = "NO" 
  /\ pc' = [ pc EXCEPT ![i] = "ABORT" ]
  /\ UNCHANGED << nSntNo, nSntYes, nSntYesF, nSntNoF, nRcvdNo, nRcvdYes, someFail >>
  
(* A correct process aborts after it received a NO message *)  
AbortSent(i) ==
  /\ pc[i] = "SENT"
  /\ nRcvdNo[i] > 0  
  /\ pc' = [ pc EXCEPT ![i] = "ABORT" ]
  /\ UNCHANGED << nSntNo, nSntYes, nSntYesF, nSntNoF, nRcvdNo, nRcvdYes, someFail >>   

(* A correct process commits since it knows that all processes propose YES *)     
Commit(i) ==
  /\ pc[i] = "SENT"     
  /\ nRcvdNo[i] = 0
  /\ nRcvdYes[i] >= N
  /\ pc' = [ pc EXCEPT ![i] = "COMMIT" ]
  /\ UNCHANGED << nSntNo, nSntYes, nSntYesF, nSntNoF, nRcvdNo, nRcvdYes, someFail >>
  
Next ==
  /\ \E self \in Proc : 
        \/ Crash(self)
        \/ Receive(self)
        \/ SendYes(self) 
        \/ SendNo(self) 
        \/ AbortNoYes(self)
        \/ AbortSent(self)
        \/ Commit(self)  
        \/ UNCHANGED vars     (* Avoid deadlocks. 
                                 After deciding, a correct process does nothing. *)

(* Type invariant *)
TypeOK == 
  /\ nSntNo \in 0..N
  /\ nSntYes \in 0..N
  /\ nSntNoF \in 0..N
  /\ nSntYesF \in 0..N    
  /\ nRcvdYes \in [ Proc -> 0..(nSntYes + nSntYesF) ]
  /\ nRcvdNo \in [ Proc -> 0..(nSntNo + nSntNoF) ] 
  /\ pc \in [ Proc -> Status ]
  /\ someFail \in [ Proc -> BOOLEAN ]      
   
(* No two correct processes decide differently. *)   
AgrrLtl ==
  [](~(\E i \in Proc, j \in Proc :  pc[i] = "COMMIT" /\ pc[j] = "ABORT"))
  
(* If some process votes NO, no process commits. *)  
AbortValidityLtl ==
  (\E i \in Proc : pc[i] = "NO") => [](\A i \in Proc : pc[i] # "COMMIT")
    
(* If every processes votes YES and no process is suspected, then no process crashes or aborts. *)    
CommitValidityLtl ==
  (\A i \in Proc : pc[i] = "YES" /\ someFail[i] = FALSE) => [](\A i \in Proc : pc[i] = "BYZ" \/ pc[i] # "ABORT")    
  
(* If no process crashes or is suspicious, then every process eventually commits. *)  
TerminationLtl ==
  ([](\A i \in Proc : pc[i] # "BYZ" /\ someFail[i] = FALSE)) => <>(\A i \in Proc : pc[i] = "COMMIT" \/ pc[i] = "ABORT")      

Agrr == (~(\E i \in Proc, j \in Proc :  pc[i] = "COMMIT" /\ pc[j] = "ABORT"))

=============================================================================
