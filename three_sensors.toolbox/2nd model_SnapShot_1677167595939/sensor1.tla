------------------------------ MODULE sensor1 ------------------------------
EXTENDS realWorld
VARIABLES fault1, noise1, signal1, hw_valid1
           
invariant_signal1 == IF fault1'=0
                    THEN signal1' = f(noise1', world_val', MAX_VAL)
                    ELSE signal1' \in MIN_VAL..MAX_VAL
                    
invariant_hw_valid1 == IF fault1'=0
                      THEN hw_valid1' = TRUE
                      ELSE hw_valid1' \in {TRUE, FALSE}

init_sensor1 == (fault1=0) /\ (noise1 \in -1..1) /\ (signal1 = f(noise1, world_val, MAX_VAL)) /\ (hw_valid1 = TRUE)

next_sensor1 == (fault1' \in 0..2) /\ (noise1' \in -1..1) /\ (signal1' \in MIN_VAL..MAX_VAL) /\ (hw_valid1 \in {TRUE, FALSE}) /\ invariant_signal1 /\ invariant_hw_valid1
           




=============================================================================
\* Modification History
\* Last modified Tue Feb 21 18:37:30 IST 2023 by 112102006
\* Created Thu Feb 02 21:42:32 IST 2023 by 112102006EXTENDS Integers, realWorld
