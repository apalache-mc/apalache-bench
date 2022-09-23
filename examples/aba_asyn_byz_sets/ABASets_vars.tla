------------------------- MODULE ABASets_vars ---------------------------------
VARIABLES
    \* The set of all sent ECHO messages (the process ids)
    \*
    \* @type: Set(Int);
    sentEcho,
    \* The set of all sent READY messages (the process ids)
    \*
    \* @type: Set(Int);
    sentReady,
    \* The set of all received ECHO messages (the process ids)
    \*
    \* @type: Int -> Set(Int);
    rcvdEcho,
    \* The set of all received READY messages (the process ids)
    \*
    \* @type: Int -> Set(Int);
    rcvdReady,
    \* The control state of a process
    \*
    \* @type: Int -> Str;
    pc

===============================================================================
