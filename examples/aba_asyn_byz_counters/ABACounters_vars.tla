------------------------- MODULE ABACounters_vars ---------------------------------

VARIABLES
    \* The counter for all sent ECHO messages
    \*
    \* @type: Int;
    sentEcho,
    \* The counter for all sent READY messages
    \*
    \* @type: Int;
    sentReady,
    \* The counter for all received ECHO messages (for each process)
    \*
    \* @type: $counter;
    rcvdEcho,
    \* The counter for all received READY messages for each process
    \*
    \* @type: $counter;
    rcvdReady,
    \* The control state of a process
    \*
    \* @type: Int -> Str;
    pc

===============================================================================
