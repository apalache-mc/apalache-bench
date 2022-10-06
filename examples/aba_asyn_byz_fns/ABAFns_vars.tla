------------------------- MODULE ABAFns_vars ---------------------------------

VARIABLES
    \* The characteristic function of the set of all sent ECHO messages (the process ids)
    \*
    \* @typeAlias: charFn = Int -> Bool;
    \* @type: $charFn;
    sentEcho,
    \* The characteristic function of the set of all sent READY messages (the process ids)
    \*
    \* @type: $charFn;
    sentReady,
    \* The characteristic function of the set of all received ECHO messages (the process ids)
    \* for each process
    \*
    \* @type: Int -> $charFn;
    rcvdEcho,
    \* The characteristic function of the set of all received READY messages (the process ids)
    \* for each process
    \*
    \* @type: Int -> $charFn;
    rcvdReady,
    \* The control state of a process
    \*
    \* @type: Int -> Str;
    pc

===============================================================================
