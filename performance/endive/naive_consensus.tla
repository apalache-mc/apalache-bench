---- MODULE naive_consensus ----
\* benchmark: ex-naive-consensus

EXTENDS TLC, FiniteSets \*, Randomization

CONSTANT
    \* @type: Set(N);
    Node,
    \* @type: Set(Set(N));
    Quorum,
    \* @type: Set(V);
    Value

VARIABLES
    \* @type: Set(<<N, V>>);
    vote,
    \* @type: Set(<<Set(N), V>>);
    decide,
    \* @type: Set(V);
    decision

vars == <<vote,decide,decision>>

VotedFor(v) == \E Q \in Quorum : <<Q,v>> \in decide

CastVote(n, v) ==
    /\ \A x \in Value : <<n,x>> \notin vote
    /\ vote' = vote \cup {<<n,v>>}
    /\ UNCHANGED <<decide, decision>>

CollectVotes(Q, v) ==
    /\ \A n \in Q : <<n,v>> \in vote
    /\ decide' = decide \cup {<<Q,v>>}
    /\ UNCHANGED <<vote, decision>>

\* @type: (Set(N), V) => Bool;
LearnValue(Q, v) ==
    /\ <<Q,v>> \in decide
    /\ decision' = decision \cup {v}
    /\ UNCHANGED <<vote, decide>>

Init == 
    /\ vote = {}
    /\ decide = {}
    /\ decision = {}

Next == 
    \/ \E n \in Node, v \in Value : CastVote(n,v)
    \/ \E Q \in Quorum, v \in Value : CollectVotes(Q,v)
    \/ \E Q \in Quorum, v \in Value : LearnValue(Q,v)

NextUnchanged == UNCHANGED vars

TypeOK == 
    /\ vote \in SUBSET (Node \X Value)
    /\ decide \in SUBSET (Quorum \X Value)
    /\ decision \in SUBSET Value

(*
\* TODO: May need to fix this.
TypeOKRandom ==
    /\ vote \in RandomSubset(20, SUBSET (Node \X Value))
    /\ decide \in RandomSubset(20, SUBSET (Quorum \X Value))
    /\ decide \in SUBSET Value
    *)

Safety == \A v1,v2 \in Value : (v1 \in decision /\ v2 \in decision) => (v1=v2)

\*Symmetry == Permutations(Node) \cup Permutations(Value)

====
