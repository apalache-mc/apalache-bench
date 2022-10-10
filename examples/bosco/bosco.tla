------------------------------- MODULE bosco -------------------------------

(* TLA+ encoding of the algorithm BOSCO considered in: 

   [1] Song, Yee Jiun, and Robbert van Renesse. "Bosco: One-step byzantine asynchronous 
   consensus." International Symposium on Distributed Computing. Springer, Berlin, 
   Heidelberg, 2008.
  
   Jure Kukovec, 2022
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

CInit ==
  /\ N = 4
  /\ T = 1
  /\ F = 1

\* The set of correct processes
Corr == 1..(N - F)

\* The set of Byzantine processes
Faulty == (N - F + 1)..N

P == 1 .. N

moreNplus3Tdiv2 == (N + 3 * T) \div 2 + 1
moreNminusTdiv2 == (N - T) \div 2 + 1

VARIABLE 
  \* @typeAlias: msgCtr = Int -> Int;
  \* @type: Int -> Str;
  pc,
  \* @type: $msgCtr;
  rcvd0,
  \* @type: $msgCtr;
  rcvd1, 
  \* @type: Int;
  sent0,
  \* @type: Int;
  sent1

\* @type: <<$msgCtr, $msgCtr>>;
rcvd == <<rcvd0, rcvd1>>
\* @type: <<Int, Int>>;
sent == <<sent0, sent1>>

Receive(self) ==
  \E r0, r1 \in Int:
    /\ rcvd0[self] <= r0
    /\ r0 <= sent0 + F
    /\ rcvd1[self] <= r1
    /\ r1 <= sent1 + F
    /\ rcvd0' = [rcvd0 EXCEPT ![self] = r0]
    /\ rcvd1' = [rcvd1 EXCEPT ![self] = r1]

UponV0(self) ==
  /\ pc[self] = "V0"
  /\ sent0' = sent0 + 1
  /\ UNCHANGED sent1
  /\ pc' = [pc EXCEPT ![self] = "S0"]        

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ sent1' = sent1 + 1
  /\ UNCHANGED sent0
  /\ pc' = [pc EXCEPT ![self] = "S1"]
                                
UponOneStep0(self) ==
  /\ pc[self] = "S0" \/ pc[self] = "S1"
  /\ \E r0 \in Int:
    /\ rcvd0' = [rcvd0 EXCEPT ![self] = r0]
    /\ r0 <= N
    /\ r0 + rcvd1[self] >= N - T \* rcvd1' = rcvd1
    /\ r0 >= moreNplus3Tdiv2
  /\ rcvd1' = rcvd1
  /\ pc' = [pc EXCEPT ![self] = "D0"]
  /\ UNCHANGED sent
                      
UponOneStep1(self) ==
  /\ pc[self] = "S0" \/ pc[self] = "S1"
  /\ \E r1 \in Int:
    /\ rcvd1' = [rcvd1 EXCEPT ![self] = r1]
    /\ r1 <= N
    /\ r1 + rcvd0[self] >= N - T \* rcvd0' = rcvd0
    /\ r1 >= moreNplus3Tdiv2
  /\ rcvd0' = rcvd0
  /\ pc' = [pc EXCEPT ![self] = "D1"]
  /\ UNCHANGED sent
                  
UponUnderlying0(self) ==
  /\ pc[self] = "S0" \/ pc[self] = "S1"
  /\ \E r0,r1 \in Int:
    /\ rcvd0' = [rcvd0 EXCEPT ![self] = r0]
    /\ rcvd1' = [rcvd1 EXCEPT ![self] = r1]
    /\ r0 < moreNplus3Tdiv2
    /\ r1 < moreNplus3Tdiv2
    /\ r0 + r1 >= N - T
    /\ r0 >= moreNminusTdiv2
    /\ r1 < moreNminusTdiv2
  /\ pc' = [pc EXCEPT ![self] = "U0"]
  /\ UNCHANGED sent

UponUnderlying1(self) ==
  /\ pc[self] = "S0" \/ pc[self] = "S1"
  /\ \E r0,r1 \in Int:
    /\ rcvd0' = [rcvd0 EXCEPT ![self] = r0]
    /\ rcvd1' = [rcvd1 EXCEPT ![self] = r1]
    /\ r0 < moreNplus3Tdiv2
    /\ r1 < moreNplus3Tdiv2
    /\ r0 + r1 >= N - T
    /\ r0 < moreNminusTdiv2
    /\ r1 >= moreNminusTdiv2
  /\ pc' = [pc EXCEPT ![self] = "U1"]   
  /\ UNCHANGED sent     
        
UponUnderlyingUndecided(self) ==
  /\\/ pc[self] = "S0" /\ pc' = [pc EXCEPT ![self] = "U0"]
    \/ pc[self] = "S1" /\ pc' = [pc EXCEPT ![self] = "U1"]       
  /\ \E r0,r1 \in Int:
    /\ rcvd0' = [rcvd0 EXCEPT ![self] = r0]
    /\ rcvd1' = [rcvd1 EXCEPT ![self] = r1]
    /\ r0 + r1 >= N - T
    /\ r0 >= moreNminusTdiv2
    /\ r1 >= moreNminusTdiv2
    /\ r0 < moreNplus3Tdiv2
    /\ r1 < moreNplus3Tdiv2
  /\ UNCHANGED sent     

Step(self) ==   
  /\ Receive(self)
  /\ \/ UponV0(self)
     \/ UponV1(self)
     \/ UponOneStep0(self)
     \/ UponOneStep1(self)                                      
     \/ UponUnderlying0(self)
     \/ UponUnderlying1(self)
     \/ UponUnderlyingUndecided(self)
     \/ pc' = pc /\ sent' = sent

(* Initial step *)
Init ==
  /\ pc \in [ Corr -> {"V0", "V1"} ]
  /\ sent0 = 0
  /\ sent1 = 0
  /\ rcvd0 = [ i \in Corr |-> 0 ]
  /\ rcvd1 = [ i \in Corr |-> 0 ]

 (* Initial step *)
Init0 ==
   /\ pc \in [ Corr -> {"V0"} ]
   /\ sent0 = 0
   /\ sent1 = 0
   /\ rcvd0 = [ i \in Corr |-> 0 ]
   /\ rcvd1 = [ i \in Corr |-> 0 ]

Next == 
  \E self \in Corr: Step(self)

TypeOK == 
  /\ sent0 \in 0..N
  /\ sent1 \in 0..N
  /\ pc \in [ Corr -> {"V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1"} ]
  /\ rcvd0 \in [ Corr -> 0..N ]
  /\ rcvd1 \in [ Corr -> 0..N ]
          
Lemma3_0 == (\E self \in Corr: (pc[self] = "D0")) => (\A self \in Corr: (pc[self] /= "D1"))  
Lemma3_1 == (\E self \in Corr: (pc[self] = "D1")) => (\A self \in Corr: (pc[self] /= "D0"))  

Lemma4_0 == (\E self \in Corr: (pc[self] = "D0")) => (\A self \in Corr: (pc[self] /= "U1"))  
Lemma4_1 == (\E self \in Corr: (pc[self] = "D1")) => (\A self \in Corr: (pc[self] /= "U0"))  

(* If there are at most 7 * T processes, these properties OneStep0 and  *)
(* OneStep1 do not hold.                                                *)
OneStep0 ==
  (\A i \in Corr: pc[i] = "V0")
    => [](\A i \in Corr:
            /\ pc[i] /= "D1"
            /\ pc[i] /= "U0"
            /\ pc[i] /= "U1")

OneStep1 ==
  (\A i \in Corr: pc[i] = "V1")
    => [](\A i \in Corr:
            /\ pc[i] /= "D0"
            /\ pc[i] /= "U0"
            /\ pc[i] /= "U1")

OneStep0Mod == \A i \in Corr:
                    /\ pc[i] /= "D1"
                    /\ pc[i] /= "U0"
                    /\ pc[i] /= "U1"

=============================================================================
