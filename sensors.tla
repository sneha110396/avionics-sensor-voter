------------------------------ MODULE sensors ------------------------------
EXTENDS Integers, realWorld
VARIABLES hw_valid, noise, fault, signal

init_sensors == (hw_valid = TRUE) /\ (noise \in -1..1) /\ (fault=0) /\ (signal \in MIN_VAL..MAX_VAL)

invariant_hw_valid == (fault'=0) => (hw_valid'=TRUE)

f(n,w,m) == CASE (w+n) > m -> m
           []   (w+n) < -m -> -m
           [] OTHER -> w+n
           
invariant_signal == IF fault'=0
                     THEN signal' = f(noise', world_val', MAX_VAL)
                     ELSE signal' \in MIN_VAL..MAX_VAL
           

next_sensors == (fault' \in 0..2) /\ (noise' \in -1..1) /\ (hw_valid' \in {TRUE, FALSE}) /\ invariant_hw_valid /\ invariant_signal



=============================================================================
\* Modification History
\* Last modified Sun Feb 05 15:26:07 IST 2023 by 112102006
\* Created Thu Feb 02 21:42:32 IST 2023 by 112102006EXTENDS Integers, realWorld
