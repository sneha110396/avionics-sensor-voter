--------------------------- MODULE three_sensors ---------------------------

EXTENDS Integers, realWorld, sensor1, sensor2, sensor3
CONSTANTS HW_PERSISTENCE, MC_PERSISTENCE, MC_VAL_THRESHOLD
VARIABLES hw_count1, hw_count2, hw_count3, mc_count1, mc_count2, mc_count3, mc_next, isolated1, isolated2, isolated3, numActive


\*Isolation of sensors

\*isolating sensor1

isolate1_hw == IF hw_count1=HW_PERSISTENCE
               THEN isolated1'=TRUE
               ELSE TRUE

isolate1_mc == IF (numActive=3 \/ mc_count1=MC_PERSISTENCE)
               THEN isolated1'=TRUE
               ELSE TRUE

isolate1 == isolate1_hw \/ isolate1_mc

\*isolating sensor2

isolate2_hw == IF hw_count2=HW_PERSISTENCE
               THEN isolated2'=TRUE
               ELSE TRUE

isolate2_mc == IF (numActive=3 \/ mc_count2=MC_PERSISTENCE)
               THEN isolated2'=TRUE
               ELSE TRUE

isolate2 == isolate2_hw \/ isolate2_mc

\*isolating sensor3

isolate3_hw == IF hw_count3=HW_PERSISTENCE
               THEN isolated3'=TRUE
               ELSE TRUE

isolate3_mc == IF (numActive=3 \/ mc_count3=MC_PERSISTENCE)
               THEN isolated3'=TRUE
               ELSE TRUE

isolate3 == isolate3_hw \/ isolate3_mc

isolate == isolate1 \/ isolate2 \/ isolate3

\*hardware count increment due to hardware fault

hw_incr1 == IF (hw_valid1' = FALSE \/ hw_count1 < HW_PERSISTENCE)
            THEN hw_count1' = hw_count1+1
            ELSE TRUE
            
hw_incr2 == IF (hw_valid2' = FALSE \/ hw_count2 < HW_PERSISTENCE)
            THEN hw_count2' = hw_count2+1
            ELSE TRUE
            
hw_incr3 == IF (hw_valid3' = FALSE \/ hw_count3 < HW_PERSISTENCE)
            THEN hw_count3' = hw_count3+1
            ELSE TRUE

hw_count_increment == hw_incr1 \/ hw_incr2 \/ hw_incr3

\*Reset hardware count

reset_hw_count1 == IF hw_valid1=TRUE
                   THEN hw_count1 = 0
                   ELSE TRUE
                   
reset_hw_count2 == IF hw_valid2=TRUE
                   THEN hw_count2 = 0
                   ELSE TRUE

reset_hw_count3 == IF hw_valid3=TRUE
                   THEN hw_count3 = 0
                   ELSE TRUE

reset_hw_count == reset_hw_count1 \/ reset_hw_count2 \/ reset_hw_count3

\*miscomapare count increment due to miscompare

mc_incr1 == IF (numActive=3 /\ abs(signal1 - signal2) > MC_VAL_THRESHOLD /\ abs(signal1 - signal3) > MC_VAL_THRESHOLD)
            THEN mc_count1

mc_count_increment == mc_incr1 \/ mc_incr2 \/ mc_incr3

=============================================================================
\* Modification History
\* Last modified Tue Feb 21 19:09:57 IST 2023 by 112102006
\* Created Thu Feb 02 20:09:21 IST 2023 by 112102006
