------------------------------ MODULE sensor2 ------------------------------
EXTENDS realWorld
VARIABLES fault2, noise2, signal2, hw_valid2
           
invariant_signal2 == IF fault2'=0
                    THEN signal2' = f(noise2', world_val', MAX_VAL)
                    ELSE signal2' \in MIN_VAL..MAX_VAL
                    
invariant_hw_valid2 == IF fault2'=0
                      THEN hw_valid2' = TRUE
                      ELSE hw_valid2' \in {TRUE, FALSE}

init_sensor2 == (fault2=0) /\ (noise2 \in -1..1) /\ (signal2 = f(noise2, world_val, MAX_VAL)) /\ (hw_valid2 = TRUE)

next_sensor2 == (fault2' \in 0..2) /\ (noise2' \in -1..1) /\ (signal2' \in MIN_VAL..MAX_VAL) /\ (hw_valid2 \in {TRUE, FALSE}) /\ invariant_signal2 /\ invariant_hw_valid2
           

=============================================================================
\* Modification History
\* Last modified Tue Feb 21 18:37:39 IST 2023 by 112102006
\* Created Tue Feb 21 18:24:07 IST 2023 by 112102006
