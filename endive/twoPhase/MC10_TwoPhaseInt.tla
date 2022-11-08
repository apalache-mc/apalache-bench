---------------------------- MODULE MC10_TwoPhaseInt ------------------------------

\* RM == { "1_OF_RM", "2_OF_RM", "3_OF_RM", "4_OF_RM", "5_OF_RM", "6_OF_RM", "7_OF_RM", "8_OF_RM", "9_OF_RM", "10_OF_RM" }
RM == {1,2,3,4,5,6,7,8,9,10}

VARIABLES
  \* @type: Int -> Str;
  rmState,
  \* @type: Str;
  tmState,
  \* @type: Set(Int);
  tmPrepared,
  \* old records. Fix soon!
  \* @type: Set([type: Str, rm: Int]);
  msgs

INSTANCE TwoPhase
===============================================================================
