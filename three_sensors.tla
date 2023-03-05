--------------------------- MODULE three_sensors ---------------------------

EXTENDS Integers, TLC
CONSTANTS HW_PERSISTENCE, MC_PERSISTENCE, MC_VAL_THRESHOLD, MAX_VAL, MIN_VAL
VARIABLES hw_count1, hw_count2, hw_count3, mc_count1, mc_count2, mc_count3, isolated1, isolated2, isolated3, numActive, outputValid

\*Generating real world signal values

world_val == RandomElement(MIN_VAL .. MAX_VAL)

\*some useful functions

f(n,w,m) == CASE (w+n) > m -> m
           []   (w+n) < -m -> -m
           [] OTHER -> w+n

abs(x) == IF x>0 THEN x ELSE -x

\*Creating sensors

noise1 == RandomElement(-1..1)
noise2 == RandomElement(-1..1)
noise3 == RandomElement(-1..1)

fault1 == RandomElement(0..2)
fault2 == RandomElement(0..2)
fault3 == RandomElement(0..2)

signal_func(noise, fault, world, max) == IF fault=0 THEN f(noise, world, max) ELSE RandomElement(-max..max)

hw_valid_func(fault) == IF fault=0 THEN TRUE ELSE RandomElement({TRUE, FALSE})
                                    
sensor1 == [signal |-> signal_func(noise1, fault1, world_val, MAX_VAL), hw_valid |-> hw_valid_func(fault1)]
sensor2 == [signal |-> signal_func(noise2, fault2, world_val, MAX_VAL), hw_valid |-> hw_valid_func(fault2)]
sensor3 == [signal |-> signal_func(noise3, fault3, world_val, MAX_VAL), hw_valid |-> hw_valid_func(fault3)]

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

\*calculating numActive

numActive_cal == \/ (isolated1'=TRUE /\ isolated2'=TRUE /\ isolated3'=TRUE /\ numActive'=0)
                 \/ (isolated1'=FALSE /\ isolated2'=TRUE /\ isolated3'=TRUE /\ numActive'=1)
                 \/ (isolated1'=TRUE /\ isolated2'=FALSE /\ isolated3'=TRUE /\ numActive'=1)
                 \/ (isolated1'=TRUE /\ isolated2'=TRUE /\ isolated3'=FALSE /\ numActive'=1)
                 \/ (isolated1'=TRUE /\ isolated2'=FALSE /\ isolated3'=FALSE /\ numActive'=2)
                 \/ (isolated1'=FALSE /\ isolated2'=TRUE /\ isolated3'=FALSE /\ numActive'=2)
                 \/ (isolated1'=FALSE /\ isolated2'=FALSE /\ isolated3'=TRUE /\ numActive'=2)
                 \/ (isolated1'=FALSE /\ isolated2'=FALSE /\ isolated3'=FALSE /\ numActive'=3)

\*hardware count increment due to hardware fault

hw_count_incr1 == IF (sensor1.hw_valid' = FALSE \/ hw_count1 < HW_PERSISTENCE)
                  THEN hw_count1' = hw_count1+1
                  ELSE FALSE
            
hw_count_incr2 == IF (sensor2.hw_valid' = FALSE \/ hw_count2 < HW_PERSISTENCE)
                  THEN hw_count2' = hw_count2+1
                  ELSE FALSE
            
hw_count_incr3 == IF (sensor3.hw_valid' = FALSE \/ hw_count3 < HW_PERSISTENCE)
                  THEN hw_count3' = hw_count3+1
                  ELSE FALSE

\*Reset hardware count

reset_hw_count1 == IF sensor1.hw_valid'=TRUE
                   THEN hw_count1' = 0
                   ELSE FALSE
                   
reset_hw_count2 == IF sensor2.hw_valid'=TRUE
                   THEN hw_count2' = 0
                   ELSE FALSE

reset_hw_count3 == IF sensor3.hw_valid'=TRUE
                   THEN hw_count3' = 0
                   ELSE FALSE

\*handling hardware count

hw_count_handling == /\ (hw_count_incr1 \/ reset_hw_count1 \/ UNCHANGED hw_count1)
                     /\ (hw_count_incr2 \/ reset_hw_count2 \/ UNCHANGED hw_count2)
                     /\ (hw_count_incr3 \/ reset_hw_count3 \/ UNCHANGED hw_count3)

\*miscomapare count increment due to miscompare with two sensors

mc_incr1 == IF (numActive=3 /\ abs(sensor1.signal' - sensor2.signal') > MC_VAL_THRESHOLD /\ abs(sensor1.signal' - sensor3.signal') > MC_VAL_THRESHOLD /\ mc_count1 < MC_PERSISTENCE)
            THEN mc_count1' = mc_count1 +1
            ELSE FALSE
            
mc_incr2 == IF (numActive=3 /\ abs(sensor1.signal' - sensor2.signal') > MC_VAL_THRESHOLD /\ abs(sensor2.signal' - sensor3.signal') > MC_VAL_THRESHOLD /\ mc_count2 < MC_PERSISTENCE)
            THEN mc_count2' = mc_count2 +1
            ELSE FALSE

mc_incr3 == IF (numActive=3 /\ abs(sensor1.signal' - sensor3.signal') > MC_VAL_THRESHOLD /\ abs(sensor2.signal' - sensor3.signal') > MC_VAL_THRESHOLD /\ mc_count3 < MC_PERSISTENCE)
            THEN mc_count3' = mc_count3 +1
            ELSE FALSE

\*reset miscompare count when there is no miscompare with atleast one sensor

reset_mc_count1 == IF (numActive=3 /\ (abs(sensor1.signal' - sensor2.signal') > MC_VAL_THRESHOLD \/ abs(sensor1.signal' - sensor3.signal') > MC_VAL_THRESHOLD))
                   THEN mc_count1' = 0
                   ELSE FALSE 
                   
reset_mc_count2 == IF (numActive=3 /\ (abs(sensor1.signal' - sensor2.signal') > MC_VAL_THRESHOLD \/ abs(sensor2.signal' - sensor3.signal') > MC_VAL_THRESHOLD))
                   THEN mc_count2' = 0
                   ELSE FALSE
                   
reset_mc_count3 == IF (numActive=3 /\ (abs(sensor1.signal' - sensor3.signal') > MC_VAL_THRESHOLD \/ abs(sensor2.signal' - sensor3.signal') > MC_VAL_THRESHOLD))
                   THEN mc_count3' = 0
                   ELSE FALSE

\*reseting all miscompare count when one sensor become isolated

reset_1 == IF (numActive=3 /\ (isolated1'=TRUE \/ isolated2'=TRUE \/ isolated3'=TRUE))
             THEN (mc_count1'=0)
             ELSE FALSE
             
reset_2 == IF (numActive=3 /\ (isolated1'=TRUE \/ isolated2'=TRUE \/ isolated3'=TRUE))
             THEN (mc_count2'=0)
             ELSE FALSE
             
reset_3 == IF (numActive=3 /\ (isolated1'=TRUE \/ isolated2'=TRUE \/ isolated3'=TRUE))
             THEN (mc_count3'=0)
             ELSE FALSE
             
\*miscomapre count increment when there are two active sensors

mc_next1 == IF (numActive=2 /\ isolated1=TRUE /\ abs(sensor2.signal' - sensor3.signal') > MC_VAL_THRESHOLD /\ mc_count1 < MC_PERSISTENCE)
            THEN mc_count1' = mc_count1+1
            ELSE FALSE
            
mc_next2 == IF (numActive=2 /\ isolated2=TRUE /\ abs(sensor1.signal' - sensor3.signal') > MC_VAL_THRESHOLD /\ mc_count2 < MC_PERSISTENCE)
            THEN mc_count2' = mc_count2+1
            ELSE FALSE

mc_next3 == IF (numActive=2 /\ isolated3=TRUE /\ abs(sensor2.signal' - sensor1.signal') > MC_VAL_THRESHOLD /\ mc_count3 < MC_PERSISTENCE)
            THEN mc_count3' = mc_count3+1
            ELSE FALSE

\*reset miscompare count when there are two active sensors

mc_reset1 == IF (numActive=2 /\ isolated1=TRUE /\ abs(sensor2.signal' - sensor3.signal') =< MC_VAL_THRESHOLD)
            THEN mc_count1' = 0
            ELSE FALSE
            
mc_reset2 == IF (numActive=2 /\ isolated2=TRUE /\ abs(sensor1.signal' - sensor3.signal') =< MC_VAL_THRESHOLD)
            THEN mc_count2' = 0
            ELSE FALSE

mc_reset3 == IF (numActive=2 /\ isolated3=TRUE /\ abs(sensor2.signal' - sensor1.signal') =< MC_VAL_THRESHOLD)
            THEN mc_count3' = 0
            ELSE FALSE
            
\*handling miscompare counts

mc_count_handling == /\ (mc_incr1 \/ reset_mc_count1 \/ reset_1 \/ mc_next1 \/ mc_reset1 \/ UNCHANGED mc_count1)
                     /\ (mc_incr2 \/ reset_mc_count2 \/ reset_2 \/ mc_next2 \/ mc_reset2 \/ UNCHANGED mc_count2)
                     /\ (mc_incr3 \/ reset_mc_count3 \/ reset_3 \/ mc_next3 \/ mc_reset3 \/ UNCHANGED mc_count3)

                 
\*calculating outputValid

outputValid_cal == CASE numActive'=3 -> outputValid'=TRUE
                   []   numActive'=2 /\ (mc_count1' < MC_PERSISTENCE) /\ (mc_count2' < MC_PERSISTENCE) /\ (mc_count3' < MC_PERSISTENCE) -> outputValid'=TRUE
                   []   numActive'=2 /\ ((mc_count1' < MC_PERSISTENCE) \/ (mc_count2' < MC_PERSISTENCE) \/ (mc_count3' < MC_PERSISTENCE)) ->outputValid'=FALSE
                   []   numActive'=1 -> outputValid'=TRUE
                   []   numActive'=0 -> outputValid'=FALSE
                   
init == (hw_count1=0) /\ (hw_count2=0) /\ (hw_count3=0) /\ (mc_count1=0) /\ (mc_count2=0) /\ (mc_count3=0) /\ (isolated1=FALSE) /\ (isolated2=FALSE) /\ (isolated3=FALSE) /\ (numActive=3) /\ (outputValid=TRUE)

next == isolation_handling /\ hw_count_handling /\ mc_count_handling /\ numActive_cal /\ outputValid_cal 
=============================================================================
\* Modification History
\* Last modified Fri Mar 03 22:08:07 IST 2023 by 112102006
\* Created Thu Feb 02 20:09:21 IST 2023 by 112102006
