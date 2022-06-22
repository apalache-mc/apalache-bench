---------------------------- MODULE MC3_TwoPhase ------------------------------

RM == { "1_OF_RM", "2_OF_RM", "3_OF_RM" }

VARIABLES
  \* @type: RM -> Str;
  rmState,
  \* @type: Str;
  tmState,
  \* @type: Set(RM);
  tmPrepared,
  \* old records. Fix soon!
  \* @type: Set([type: Str, rm: RM]);
  msgs

INSTANCE TwoPhase
===============================================================================
