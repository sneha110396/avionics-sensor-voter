--------------------------- MODULE three_sensors ---------------------------

EXTENDS Integers, realWorld, sensor1, sensor2, sensor3
CONSTANTS HW_PERSISTENCE, MC_PERSISTENCE, MC_VAL_THRESHOLD
VARIABLES hw_count1, hw_count2, hw_count3, mc_count1, mc_count2, mc_count3, isolated1, isolated2, isolated3, numActive, outputValid


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

\*miscomapare count increment due to miscompare with two sensors

mc_incr1 == IF (numActive'=3 /\ abs(signal1' - signal2') > MC_VAL_THRESHOLD /\ abs(signal1' - signal3') > MC_VAL_THRESHOLD /\ mc_count1 < MC_PERSISTENCE)
            THEN mc_count1' = mc_count1 +1
            ELSE TRUE
            
mc_incr2 == IF (numActive'=3 /\ abs(signal1' - signal2') > MC_VAL_THRESHOLD /\ abs(signal2' - signal3') > MC_VAL_THRESHOLD /\ mc_count2 < MC_PERSISTENCE)
            THEN mc_count2' = mc_count2 +1
            ELSE TRUE

mc_incr3 == IF (numActive'=3 /\ abs(signal1' - signal3') > MC_VAL_THRESHOLD /\ abs(signal2' - signal3') > MC_VAL_THRESHOLD /\ mc_count3 < MC_PERSISTENCE)
            THEN mc_count3' = mc_count3 +1
            ELSE TRUE

\*reset miscompare count when there is no miscompare with atleast one sensor

reset_mc_count1 == IF (numActive'=3 /\ (abs(signal1' - signal2') > MC_VAL_THRESHOLD \/ abs(signal1' - signal3') > MC_VAL_THRESHOLD))
                   THEN mc_count1' = 0
                   ELSE TRUE 
                   
reset_mc_count2 == IF (numActive'=3 /\ (abs(signal1' - signal2') > MC_VAL_THRESHOLD \/ abs(signal2' - signal3') > MC_VAL_THRESHOLD))
                   THEN mc_count2' = 0
                   ELSE TRUE
                   
reset_mc_count3 == IF (numActive'=3 /\ (abs(signal1' - signal3') > MC_VAL_THRESHOLD \/ abs(signal2' - signal3') > MC_VAL_THRESHOLD))
                   THEN mc_count3' = 0
                   ELSE TRUE

\*reseting all miscompare count when one sensor become isolated

reset_all == IF (numActive=3 /\ numActive'=2)
             THEN (mc_count1'=0) /\ (mc_count2'=0) /\ (mc_count3'=0)
             ELSE TRUE
             
\*miscomapre count increment when there are two active sensors

mc_next1 == IF (numActive=2 /\ isolated1=TRUE /\ abs(signal2' - signal3') > MC_VAL_THRESHOLD /\ mc_count1 < MC_PERSISTENCE)
            THEN mc_count1' = mc_count1+1
            ELSE TRUE
            
mc_next2 == IF (numActive=2 /\ isolated2=TRUE /\ abs(signal1' - signal3') > MC_VAL_THRESHOLD /\ mc_count2 < MC_PERSISTENCE)
            THEN mc_count2' = mc_count2+1
            ELSE TRUE

mc_next3 == IF (numActive=2 /\ isolated3=TRUE /\ abs(signal2' - signal1') > MC_VAL_THRESHOLD /\ mc_count3 < MC_PERSISTENCE)
            THEN mc_count3' = mc_count3+1
            ELSE TRUE
            
mc_count_increment == mc_incr1 \/ mc_incr2 \/ mc_incr3 \/ mc_next1 \/ mc_next2 \/ mc_next3

\*reset miscompare count when there are two active sensors

mc_reset1 == IF (numActive=2 /\ isolated1=TRUE /\ abs(signal2' - signal3') =< MC_VAL_THRESHOLD)
            THEN mc_count1' = 0
            ELSE TRUE
            
mc_reset2 == IF (numActive=2 /\ isolated2=TRUE /\ abs(signal1' - signal3') =< MC_VAL_THRESHOLD)
            THEN mc_count2' = 0
            ELSE TRUE

mc_reset3 == IF (numActive=2 /\ isolated3=TRUE /\ abs(signal2' - signal1') =< MC_VAL_THRESHOLD)
            THEN mc_count3' = 0
            ELSE TRUE
            
reset_mc_count == reset_mc_count1 \/ reset_mc_count2 \/ reset_mc_count3 \/ mc_reset1 \/ mc_reset2 \/ mc_reset3

\*calculating numActive

numActive_cal == CASE (isolated1=TRUE /\ isolated2=TRUE /\ isolated3=TRUE) -> numActive=0
                 []   (isolated1=FALSE /\ isolated2=TRUE /\ isolated3=TRUE) -> numActive=1
                 []   (isolated1=TRUE /\ isolated2=FALSE /\ isolated3=TRUE) -> numActive=1
                 []   (isolated1=TRUE /\ isolated2=TRUE /\ isolated3=FALSE) -> numActive=1
                 []   (isolated1=TRUE /\ isolated2=FALSE /\ isolated3=FALSE) -> numActive=2
                 []   (isolated1=FALSE /\ isolated2=TRUE /\ isolated3=FALSE) -> numActive=2
                 []   (isolated1=FALSE /\ isolated2=FALSE /\ isolated3=TRUE) -> numActive=2
                 []OTHER -> numActive =3
=============================================================================
\* Modification History
\* Last modified Wed Feb 22 19:19:33 IST 2023 by 112102006
\* Created Thu Feb 02 20:09:21 IST 2023 by 112102006
