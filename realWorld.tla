----------------------------- MODULE realWorld -----------------------------
EXTENDS TLC, Integers
CONSTANTS MAX_VAL, MIN_VAL

world_val == CHOOSE x \in MIN_VAL..MAX_VAL : TRUE

=============================================================================
\* Modification History
\* Last modified Sun Feb 19 19:07:58 IST 2023 by 112102006
\* Created Thu Feb 02 20:26:30 IST 2023 by 112102006
