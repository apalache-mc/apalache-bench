---------------------------- MODULE floodmin ----------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Set(Int);
    Values,
    \* @type: Int;
    N,
    \* @type: Int;
    T,
    \* @type: Int;
    F,
    \* @type: Int;
    K

VARIABLES
    \* @type: Int -> { min: Int, decision: Int };
    state,
    \* @type: Int -> (Int -> Int);
    msgs,
    \* @type: Int;
    round,
    \* @type: Str;
    phase,
    \* @type: Set(Int);
    crash,
    \* @type: Set(Int);
    failed,
    \* @type: Int -> Set(Int);
    receivers
      
vars == <<state, msgs, round, phase, crash, failed, receivers>>

P == 1 .. N
Nil == -1

ValuesOrNil == Values \union { Nil }

C == [ min : Values, decision : ValuesOrNil ]
InitC == [ min : Values, decision : { Nil }]

InitEnvironment ==
    /\ phase = "msgs"
    /\ round = 0
    /\ crash \in SUBSET(P)
    /\ failed = {}
    /\ Cardinality(failed \cup crash) <= F
    /\ receivers \in [crash -> SUBSET(P)]
    
InitAlgorithm ==
    /\ state \in [P -> InitC]
    /\ msgs = [p \in P |-> [q \in P |-> Nil]] \* two-dimensional messages array
    
Min(S) == CHOOSE v \in S: \A w \in S: v <= w

Msgs(p) == IF p \in failed
        THEN {}
        ELSE {
          v \in Values: \E q \in P : msgs[q][p] # Nil /\ msgs[q][p] = v
        }
  
    
SendMessage(p, q) ==
    state[p].min

EnvSemMsg(m, p, q) ==
    IF \/ p \in failed
       \/ p \in crash /\ q \notin receivers[p]
    THEN Nil
    ELSE m
    
\* @type: (Int, { min: Int, decision: Int }, { min: Int, decision: Int }) => { min: Int, decision: Int };
EnvSemState(p, s1, s2) ==
    IF p \in failed \/ p \in crash \/ s2.decision # Nil
    THEN s2
    ELSE s1

Update(s, X) ==
    LET m == Min(X) IN
    LET d == IF round >= (T \div K) + 1
             THEN m
             ELSE Nil
    IN
    [min |-> m, decision |-> d]

TransStep ==
    \* the algorithm
    /\ state' = [p \in P |-> EnvSemState(p, Update(state[p], Msgs(p)), state[p])]
    /\ msgs' = [p \in P |-> [q \in P |-> Nil]]
    \* the environment
    /\ phase' = "msgs"
    /\ failed' = failed \cup crash
    /\ crash' \in SUBSET(P \ failed')
    /\ Cardinality(failed' \cup crash') <= F
    /\ receivers' \in [crash' -> SUBSET(P)]
    /\ UNCHANGED round
    
MsgsStep ==
    IF round <= T \div K
    THEN
    \* the algorithm
    /\ msgs' = [p \in P |-> [q \in P |-> EnvSemMsg(SendMessage(p, q), p, q)]]
    /\ UNCHANGED state
    \* the environment
    /\ phase' = "trans"
    /\ round' = round+1
    /\ UNCHANGED <<crash, failed, receivers>>
    ELSE UNCHANGED vars

\* next state action predicates
Init ==
    InitAlgorithm /\ InitEnvironment

Next ==
    \/ phase = "msgs" /\ MsgsStep
    \/ phase = "trans" /\ TransStep

\* fairness constraint
Fairness == WF_vars(Next)

\* specification
Spec == Init /\ [][Next]_vars /\ Fairness
                 
\* safety properties
Agreement == \E W \in SUBSET(Values) : Cardinality(W) = K /\ [](\A q \in P : (q \notin failed /\ state[q].decision # Nil) => state[q].decision \in W)

Validity == \A I \in SUBSET(Values) : I = {state[p].min : p \in P} => [](\A p \in P : (state[p].decision # Nil => state[p].decision \in I))

\* safety as invariant
AgreementInv ==
  \E W \in SUBSET(Values):
    /\ Cardinality(W) = K
    /\ \A q \in P:
         (q \notin failed /\ state[q].decision # Nil)
           => state[q].decision \in W

ValidityInv ==
  \A I \in SUBSET(Values):
    I = { state[p].min : p \in P }
      => \A p \in P:
           state[p].decision # Nil => state[p].decision \in I

\* liveness property
Termination == <>(\A p \in P : p \in failed \/ state[p].decision # Nil)



=============================================================================
\* Modification History
\* Last modified Thu Sep 28 18:11:32 CEST 2017 by stoilkov
\* Created Thu Sep 28 18:06:12 CEST 2017 by stoilkov
