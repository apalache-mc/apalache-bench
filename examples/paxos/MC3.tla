----------------------------- MODULE MC3 ------------------------------
EXTENDS Integers

\* We are using uninterpreted types to improve performance of Apalache:
\* https://apalache.informal.systems/docs/HOWTOs/uninterpretedTypes.html
Acceptor == {
    "1_OF_A",
    "2_OF_A",
    "3_OF_A"
}
Value == {
    "1_OF_V",
    "2_OF_V"
}
Quorum == {
    { "1_OF_A", "2_OF_A" },
    { "1_OF_A", "3_OF_A" },
    { "2_OF_A", "3_OF_A" }
}

VARIABLE
    \* @type: A -> Int;
    maxBal,
    \* @type: A -> Int;
    maxVBal,
    \* @type: A -> V;
    maxVal,
    \* TODO: use the variant type when it becomes available:
    \* https://github.com/informalsystems/apalache/issues/401
    \* @type: Set([type: Str, bal: Int, acc: A, val: V]);
    msgs

\* Apalache does not have any problem drawing values from Nat.
\* However, we need a finite set to prove inductive invariants.
OVERRIDE_Ballot == 0..10

INSTANCE Paxos

=============================================================================

