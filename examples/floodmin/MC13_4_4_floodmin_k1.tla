----------------------- MODULE MC13_4_4_floodmin_k1 ----------------------------
EXTENDS floodmin_vars

\* N > 3 * T and T >= F
\* length is 2 * (T + 1)

Values == { 0, 1 }
N == 13
T == 4
F == 4
K == 1

INSTANCE floodmin
===============================================================================
