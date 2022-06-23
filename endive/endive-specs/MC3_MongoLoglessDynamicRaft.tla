----------------- MODULE MC3_MongoLoglessDynamicRaft --------------------------
Server      == { "1_OF_S", "2_OF_S", "3_OF_S" }
Secondary   == "Secondary"
Primary     == "Primary"
Nil         == "Nil"
InitTerm    == 1
MaxTerm     == 4
MaxLogLen   == 4
MaxConfigVersion    == 3

VARIABLE
    \* @type: S -> Int;
    currentTerm, \* counter.
    \* @type: S -> Str;
    state,
    \* @type: S -> Int;
    configVersion, \* counter.
    \* @type: S -> Int;
    configTerm, \* counter.
    \* @type: S -> Set(S);
    config

INSTANCE MongoLoglessDynamicRaft
================================================================================
