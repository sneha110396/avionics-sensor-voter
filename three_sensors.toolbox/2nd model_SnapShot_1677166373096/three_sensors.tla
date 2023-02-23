--------------------------- MODULE three_sensors ---------------------------

EXTENDS Integers, realWorld, sensor1, sensor2, sensor3
CONSTANTS HW_PERSISTENCE, MC_PERSISTENCE, MC_VAL_THRESHOLD
VARIABLES hw_count1, hw_count2, hw_count3, mc_count1, mc_count2, mc_count3, isolated1, isolated2, isolated3, numActive, outputValid


\*Isolation of sensors

\*isolating sensor1

isolate1_hw == IF hw_count1=HW_PERSISTENCE
               THEN isolated1'=TRUE
               ELSE FALSE

isolate1_mc == IF (numActive=3 \/ mc_count1=MC_PERSISTENCE)
               THEN isolated1'=TRUE
               ELSE FALSE

isolate1 == isolate1_hw \/ isolate1_mc

\*isolating sensor2

isolate2_hw == IF hw_count2=HW_PERSISTENCE
               THEN isolated2'=TRUE
               ELSE FALSE

isolate2_mc == IF (numActive=3 \/ mc_count2=MC_PERSISTENCE)
               THEN isolated2'=TRUE
               ELSE FALSE

isolate2 == isolate2_hw \/ isolate2_mc

\*isolating sensor3

isolate3_hw == IF hw_count3=HW_PERSISTENCE
               THEN isolated3'=TRUE
               ELSE FALSE

isolate3_mc == IF (numActive=3 \/ mc_count3=MC_PERSISTENCE)
               THEN isolated3'=TRUE
               ELSE FALSE

isolate3 == isolate3_hw \/ isolate3_mc

isolation_handling == (isolate1 \/ UNCHANGED isolated1) /\ (isolate2 \/ UNCHANGED isolated2) /\ (isolate3 \/ UNCHANGED isolated3)

\*hardware count increment due to hardware fault

hw_count_incr1 == IF (hw_valid1' = FALSE \/ hw_count1 < HW_PERSISTENCE)
                  THEN hw_count1' = hw_count1+1
                  ELSE TRUE
            
hw_count_incr2 == IF (hw_valid2' = FALSE \/ hw_count2 < HW_PERSISTENCE)
                  THEN hw_count2' = hw_count2+1
                  ELSE TRUE
            
hw_count_incr3 == IF (hw_valid3' = FALSE \/ hw_count3 < HW_PERSISTENCE)
                  THEN hw_count3' = hw_count3+1
                  ELSE TRUE

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

\*handling hardware count

hw_count_handling == /\ (hw_count_incr1 \/ reset_hw_count1 \/ UNCHANGED hw_count1)
                     /\ (hw_count_incr2 \/ reset_hw_count2 \/ UNCHANGED hw_count2)
                     /\ (hw_count_incr3 \/ reset_hw_count3 \/ UNCHANGED hw_count3)

\*miscomapare count increment due to miscompare with two sensors

mc_incr1 == IF (numActive'=3 /\ abs(signal1' - signal2') > MC_VAL_THRESHOLD /\ abs(signal1' - signal3') > MC_VAL_THRESHOLD /\ mc_count1 < MC_PERSISTENCE)
            THEN mc_count1' = mc_count1 +1
            ELSE FALSE
            
mc_incr2 == IF (numActive'=3 /\ abs(signal1' - signal2') > MC_VAL_THRESHOLD /\ abs(signal2' - signal3') > MC_VAL_THRESHOLD /\ mc_count2 < MC_PERSISTENCE)
            THEN mc_count2' = mc_count2 +1
            ELSE FALSE

mc_incr3 == IF (numActive'=3 /\ abs(signal1' - signal3') > MC_VAL_THRESHOLD /\ abs(signal2' - signal3') > MC_VAL_THRESHOLD /\ mc_count3 < MC_PERSISTENCE)
            THEN mc_count3' = mc_count3 +1
            ELSE FALSE

\*reset miscompare count when there is no miscompare with atleast one sensor

reset_mc_count1 == IF (numActive'=3 /\ (abs(signal1' - signal2') > MC_VAL_THRESHOLD \/ abs(signal1' - signal3') > MC_VAL_THRESHOLD))
                   THEN mc_count1' = 0
                   ELSE FALSE 
                   
reset_mc_count2 == IF (numActive'=3 /\ (abs(signal1' - signal2') > MC_VAL_THRESHOLD \/ abs(signal2' - signal3') > MC_VAL_THRESHOLD))
                   THEN mc_count2' = 0
                   ELSE FALSE
                   
reset_mc_count3 == IF (numActive'=3 /\ (abs(signal1' - signal3') > MC_VAL_THRESHOLD \/ abs(signal2' - signal3') > MC_VAL_THRESHOLD))
                   THEN mc_count3' = 0
                   ELSE FALSE

\*reseting all miscompare count when one sensor become isolated

reset_1 == IF (numActive=3 /\ numActive'=2)
             THEN (mc_count1'=0)
             ELSE FALSE
             
reset_2 == IF (numActive=3 /\ numActive'=2)
             THEN (mc_count2'=0)
             ELSE FALSE
             
reset_3 == IF (numActive=3 /\ numActive'=2)
             THEN (mc_count3'=0)
             ELSE FALSE
             
\*miscomapre count increment when there are two active sensors

mc_next1 == IF (numActive=2 /\ isolated1=TRUE /\ abs(signal2' - signal3') > MC_VAL_THRESHOLD /\ mc_count1 < MC_PERSISTENCE)
            THEN mc_count1' = mc_count1+1
            ELSE FALSE
            
mc_next2 == IF (numActive=2 /\ isolated2=TRUE /\ abs(signal1' - signal3') > MC_VAL_THRESHOLD /\ mc_count2 < MC_PERSISTENCE)
            THEN mc_count2' = mc_count2+1
            ELSE FALSE

mc_next3 == IF (numActive=2 /\ isolated3=TRUE /\ abs(signal2' - signal1') > MC_VAL_THRESHOLD /\ mc_count3 < MC_PERSISTENCE)
            THEN mc_count3' = mc_count3+1
            ELSE FALSE

\*reset miscompare count when there are two active sensors

mc_reset1 == IF (numActive=2 /\ isolated1=TRUE /\ abs(signal2' - signal3') =< MC_VAL_THRESHOLD)
            THEN mc_count1' = 0
            ELSE FALSE
            
mc_reset2 == IF (numActive=2 /\ isolated2=TRUE /\ abs(signal1' - signal3') =< MC_VAL_THRESHOLD)
            THEN mc_count2' = 0
            ELSE FALSE

mc_reset3 == IF (numActive=2 /\ isolated3=TRUE /\ abs(signal2' - signal1') =< MC_VAL_THRESHOLD)
            THEN mc_count3' = 0
            ELSE FALSE
            
\*handling miscompare counts

mc_count_handling == /\ (mc_incr1 \/ reset_mc_count1 \/ reset_1 \/ mc_next1 \/ mc_reset1 \/ UNCHANGED mc_count1)
                     /\ (mc_incr2 \/ reset_mc_count2 \/ reset_2 \/ mc_next2 \/ mc_reset2 \/ UNCHANGED mc_count2)
                     /\ (mc_incr3 \/ reset_mc_count3 \/ reset_3 \/ mc_next3 \/ mc_reset3 \/ UNCHANGED mc_count3)

\*calculating numActive

numActive_cal == CASE (isolated1'=TRUE /\ isolated2'=TRUE /\ isolated3'=TRUE) -> numActive'=0
                 []   (isolated1'=FALSE /\ isolated2'=TRUE /\ isolated3'=TRUE) -> numActive'=1
                 []   (isolated1'=TRUE /\ isolated2'=FALSE /\ isolated3'=TRUE) -> numActive'=1
                 []   (isolated1'=TRUE /\ isolated2'=TRUE /\ isolated3'=FALSE) -> numActive'=1
                 []   (isolated1'=TRUE /\ isolated2'=FALSE /\ isolated3'=FALSE) -> numActive'=2
                 []   (isolated1'=FALSE /\ isolated2'=TRUE /\ isolated3'=FALSE) -> numActive'=2
                 []   (isolated1'=FALSE /\ isolated2'=FALSE /\ isolated3'=TRUE) -> numActive'=2
                 []OTHER -> numActive' =3
                 
\*calculating outputValid

outputValid_cal == CASE numActive'=3 -> outputValid'=TRUE
                   []   numActive'=2 /\ (mc_count1' < MC_PERSISTENCE) /\ (mc_count2' < MC_PERSISTENCE) /\ (mc_count3' < MC_PERSISTENCE) -> outputValid'=TRUE
                   []   numActive'=2 /\ ((mc_count1' < MC_PERSISTENCE) \/ (mc_count2' < MC_PERSISTENCE) \/ (mc_count3' < MC_PERSISTENCE)) ->outputValid'=FALSE
                   []   numActive'=1 -> outputValid'=TRUE
                   []   numActive'=0 -> outputValid'=FALSE
                   
init1 == (hw_count1=0) /\ (hw_count2=0) /\ (hw_count3=0) /\ (mc_count1=0) /\ (mc_count2=0) /\ (mc_count3=0) /\ (isolated1=FALSE) /\ (isolated2=FALSE) /\ (isolated3=FALSE) /\ (numActive=3) /\ (outputValid=TRUE)
init == init1 /\ init_world /\ init_sensor1 /\ init_sensor2 /\ init_sensor3
next == next_world /\ next_sensor1 /\ next_sensor2 /\ next_sensor3 /\ isolation_handling /\ hw_count_handling /\ mc_count_handling /\ numActive_cal /\ outputValid_cal 
=============================================================================
\* Modification History
\* Last modified Thu Feb 23 21:02:43 IST 2023 by 112102006
\* Created Thu Feb 02 20:09:21 IST 2023 by 112102006
