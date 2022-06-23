---------------------- MODULE MC3_learning_switch -----------------------------
Node == { "1", "2", "3" }

VARIABLE 
    \* @type: Set(<<Str, Str, Str>>);
    table,
    \* @type: Set(<<Str, Str, Str, Str>>);
    pending

INSTANCE learning_switch
===============================================================================
