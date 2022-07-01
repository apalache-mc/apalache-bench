----------------- MODULE MC10_MongoLoglessDynamicRaft --------------------------
Server      == { "1_OF_S", "2_OF_S", "3_OF_S", "4_OF_S", "5_OF_S", "6_OF_S", "7_OF_S", "8_OF_S", "9_OF_S", "10_OF_S" }
Secondary   == "Secondary"
Primary     == "Primary"
Nil         == "Nil"
InitTerm    == 1
MaxTerm     == 11
MaxLogLen   == 11
MaxConfigVersion    == 10

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
