-------------------------- MODULE floodmin_vars -------------------------------
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

===============================================================================
