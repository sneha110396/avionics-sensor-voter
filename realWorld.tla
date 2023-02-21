----------------------------- MODULE realWorld -----------------------------
EXTENDS Integers
CONSTANTS MAX_VAL, MIN_VAL
VARIABLE world_val

init_world == world_val \in -6..6
next_world == world_val \in -6..6

f(n,w,m) == CASE (w+n) > m -> m
           []   (w+n) < -m -> -m
           [] OTHER -> w+n

abs(x) == IF x>0 THEN x ELSE -x
=============================================================================
\* Modification History
\* Last modified Tue Feb 21 19:02:29 IST 2023 by 112102006
\* Created Thu Feb 02 20:26:30 IST 2023 by 112102006
