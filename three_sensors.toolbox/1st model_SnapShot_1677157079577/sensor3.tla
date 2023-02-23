------------------------------ MODULE sensor3 ------------------------------
EXTENDS realWorld
VARIABLES fault3, noise3, signal3, hw_valid3
           
invariant_signal3 == IF fault3'=0
                    THEN signal3' = f(noise3', world_val', MAX_VAL)
                    ELSE signal3' \in MIN_VAL..MAX_VAL
                    
invariant_hw_valid3 == IF fault3'=0
                      THEN hw_valid3' = TRUE
                      ELSE hw_valid3' \in {TRUE, FALSE}

init_sensor3 == (fault3=0) /\ (noise3 \in -1..1) /\ (signal3 = f(noise3, world_val, MAX_VAL)) /\ (hw_valid3 = TRUE)

next_sensor3 == (fault3' \in 0..2) /\ (noise3' \in -1..1) /\ (signal3' \in MIN_VAL..MAX_VAL) /\ (hw_valid3 \in {TRUE, FALSE}) /\ invariant_signal3 /\ invariant_hw_valid3
           

=============================================================================
\* Modification History
\* Last modified Tue Feb 21 18:37:49 IST 2023 by 112102006
\* Created Tue Feb 21 18:29:51 IST 2023 by 112102006
