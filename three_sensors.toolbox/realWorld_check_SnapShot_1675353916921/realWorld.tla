----------------------------- MODULE realWorld -----------------------------
EXTENDS Integers
VARIABLES world_val
CONSTANTS MAX_VAL, MIN_VAL

init_world == world_val \in MIN_VAL..MAX_VAL
next_world == world_val \in MIN_VAL..MAX_VAL


=============================================================================
\* Modification History
\* Last modified Thu Feb 02 21:31:12 IST 2023 by 112102006
\* Created Thu Feb 02 20:26:30 IST 2023 by 112102006
