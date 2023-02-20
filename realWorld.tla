----------------------------- MODULE realWorld -----------------------------
EXTENDS Integers
CONSTANTS MAX_VAL, MIN_VAL
VARIABLE world_val

init_world == world_val \in -6..6
next_world == world_val \in -6..6

=============================================================================
\* Modification History
\* Last modified Mon Feb 20 18:53:19 IST 2023 by 112102006
\* Created Thu Feb 02 20:26:30 IST 2023 by 112102006
