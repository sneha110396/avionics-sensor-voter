------------------------------ MODULE sensors ------------------------------
EXTENDS realWorld
VARIABLES fault, noise, signal, hw_valid

f(n,w,m) == CASE (w+n) > m -> m
           []   (w+n) < -m -> -m
           [] OTHER -> w+n
           
invariant_signal == IF fault'=0
                    THEN signal' = f(noise', world_val', MAX_VAL)
                    ELSE signal' \in MIN_VAL..MAX_VAL
                    
invariant_hw_valid == IF fault'=0
                      THEN hw_valid' = TRUE
                      ELSE hw_valid' \in {TRUE, FALSE}

init_sensors == (fault=0) /\ (noise \in -1..1) /\ (signal = f(noise, world_val, MAX_VAL)) /\ (hw_valid = TRUE)

next_sensors == (fault' \in 0..2) /\ (noise' \in -1..1) /\ (signal' \in MIN_VAL..MAX_VAL) /\ (hw_valid \in {TRUE, FALSE}) /\ invariant_signal /\ invariant_hw_valid
           




=============================================================================
\* Modification History
\* Last modified Mon Feb 20 19:08:52 IST 2023 by 112102006
\* Created Thu Feb 02 21:42:32 IST 2023 by 112102006EXTENDS Integers, realWorld
