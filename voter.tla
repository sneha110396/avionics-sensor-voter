------------------------------- MODULE voter -------------------------------

EXTENDS Integers, TLC, Sequences
CONSTANTS HW_PERSISTENCE, MC_PERSISTENCE, MC_VAL_THRESHOLD, MAX_VAL, MIN_VAL
VARIABLES world_val, noise1, noise2, noise3, fault1, fault2, fault3, numActive, outputValid, hw_count1, hw_count2, hw_count3, mc_count1, mc_count2, mc_count3, isolated1, isolated2, isolated3 

init == (world_val \in MIN_VAL..MAX_VAL) /\ (noise1 \in -1..1) /\ (noise2 \in -1..1) /\ (noise3 \in -1..1) /\ (fault1 \in 0..2) /\ (fault2 \in 0..2) /\ (fault3 \in 0..2) /\ (hw_count1=0) /\ (hw_count2=0) /\ (hw_count3=0) /\ (mc_count1=0) /\ (mc_count2=0) /\ (mc_count3=0) /\ (isolated1=FALSE) /\ (isolated2=FALSE) /\ (isolated3=FALSE) /\ (numActive=3) /\ (outputValid=TRUE)

\*calculating world_val

next_world_val == CASE (world_val < MAX_VAL) /\ (world_val > MIN_VAL) -> (world_val'= world_val+1) \/ (world_val'=world_val-1) \/ (world_val'=world_val)
                  [] (world_val = MAX_VAL) -> (world_val'=world_val-1) \/ (world_val'=world_val)
                  [] (world_val = MIN_VAL) -> (world_val'=world_val+1) \/ (world_val'=world_val)
                  [] OTHER -> UNCHANGED world_val

\*some useful functions

f(n,w,m) == CASE (w+n) > m -> m
           []   (w+n) < -m -> -m
           [] OTHER -> w+n

abs(x) == IF x>0 THEN x ELSE -x

\*Creating sensors

signal_func(noise, fault, world, max) == IF fault=0 THEN f(noise, world, max) ELSE RandomElement(-max..max)

hw_valid_func(fault) == IF fault=0 THEN TRUE ELSE RandomElement({TRUE, FALSE})

sensor1 == [signal |-> signal_func(noise1, fault1, world_val, MAX_VAL), hw_valid |-> hw_valid_func(fault1)]
sensor2 == [signal |-> signal_func(noise2, fault2, world_val, MAX_VAL), hw_valid |-> hw_valid_func(fault2)]
sensor3 == [signal |-> signal_func(noise3, fault3, world_val, MAX_VAL), hw_valid |-> hw_valid_func(fault3)]
                                    


\*calculating isolated1, isolated2, isolated3

next_isolated1 == IF ((hw_count1=HW_PERSISTENCE) \/ (numActive=3 \/ mc_count1=MC_PERSISTENCE)) \/ (isolated1=TRUE)
                  THEN isolated1' = TRUE 
                  ELSE isolated1' = FALSE
                  
next_isolated2 == IF ((hw_count2=HW_PERSISTENCE) \/ (numActive=3 \/ mc_count2=MC_PERSISTENCE)) \/ (isolated2=TRUE)
                  THEN isolated2' = TRUE 
                  ELSE isolated2' = FALSE
                  
next_isolated3 == IF ((hw_count3=HW_PERSISTENCE) \/ (numActive=3 \/ mc_count3=MC_PERSISTENCE)) \/ (isolated3=TRUE)
                  THEN isolated3' = TRUE 
                  ELSE isolated3' = FALSE
               



\*calculating numActive

numActive_cal == \/ (isolated1'=TRUE /\ isolated2'=TRUE /\ isolated3'=TRUE /\ numActive'=0)
                 \/ (isolated1'=FALSE /\ isolated2'=TRUE /\ isolated3'=TRUE /\ numActive'=1)
                 \/ (isolated1'=TRUE /\ isolated2'=FALSE /\ isolated3'=TRUE /\ numActive'=1)
                 \/ (isolated1'=TRUE /\ isolated2'=TRUE /\ isolated3'=FALSE /\ numActive'=1)
                 \/ (isolated1'=TRUE /\ isolated2'=FALSE /\ isolated3'=FALSE /\ numActive'=2)
                 \/ (isolated1'=FALSE /\ isolated2'=TRUE /\ isolated3'=FALSE /\ numActive'=2)
                 \/ (isolated1'=FALSE /\ isolated2'=FALSE /\ isolated3'=TRUE /\ numActive'=2)
                 \/ (isolated1'=FALSE /\ isolated2'=FALSE /\ isolated3'=FALSE /\ numActive'=3)

\*calculating hardware counts

next_hw_count1 == CASE (sensor1.hw_valid' = FALSE \/ hw_count1 < HW_PERSISTENCE) -> (hw_count1' = hw_count1+1)
                  [] (sensor1.hw_valid'=TRUE) -> (hw_count1' = 0)
                  [] (hw_count1=HW_PERSISTENCE) -> (hw_count1'=HW_PERSISTENCE)
                  [] OTHER -> UNCHANGED hw_count1
                  
next_hw_count2 == CASE (sensor2.hw_valid' = FALSE \/ hw_count2 < HW_PERSISTENCE) -> (hw_count2' = hw_count2+1)
                  [] (sensor2.hw_valid'=TRUE) -> (hw_count2' = 0)
                  [] (hw_count2=HW_PERSISTENCE) -> (hw_count2'=HW_PERSISTENCE)
                  [] OTHER -> UNCHANGED hw_count2
                  
next_hw_count3 == CASE (sensor3.hw_valid' = FALSE \/ hw_count3 < HW_PERSISTENCE) -> (hw_count3' = hw_count3+1)
                  [] (sensor3.hw_valid'=TRUE) -> (hw_count3' = 0)
                  [] (hw_count3=HW_PERSISTENCE) -> (hw_count3'=HW_PERSISTENCE)
                  [] OTHER -> UNCHANGED hw_count3         


\*calculating miscompare counts

next_mc_count1 == CASE ((numActive=3 /\ abs(sensor1.signal' - sensor2.signal') > MC_VAL_THRESHOLD /\ abs(sensor1.signal' - sensor3.signal') > MC_VAL_THRESHOLD /\ mc_count1 < MC_PERSISTENCE)) -> (mc_count1' = mc_count1 +1)
                  [] (numActive=3 /\ (abs(sensor1.signal' - sensor2.signal') > MC_VAL_THRESHOLD \/ abs(sensor1.signal' - sensor3.signal') > MC_VAL_THRESHOLD)) -> mc_count1' = 0
                  [] (numActive=3 /\ (isolated1'=TRUE \/ isolated2'=TRUE \/ isolated3'=TRUE)) -> (mc_count1'=0)
                  [] (numActive=2 /\ isolated1=TRUE /\ abs(sensor2.signal' - sensor3.signal') > MC_VAL_THRESHOLD /\ mc_count1 < MC_PERSISTENCE) -> (mc_count1' = mc_count1+1)
                  [] (numActive=2 /\ isolated1=TRUE /\ abs(sensor2.signal' - sensor3.signal') =< MC_VAL_THRESHOLD) -> (mc_count1' = 0)
                  [] OTHER -> UNCHANGED mc_count1

next_mc_count2 == CASE ((numActive=3 /\ abs(sensor1.signal' - sensor2.signal') > MC_VAL_THRESHOLD /\ abs(sensor2.signal' - sensor3.signal') > MC_VAL_THRESHOLD /\ mc_count2 < MC_PERSISTENCE)) -> (mc_count2' = mc_count2 +1)
                  [] (numActive=3 /\ (abs(sensor1.signal' - sensor2.signal') > MC_VAL_THRESHOLD \/ abs(sensor2.signal' - sensor3.signal') > MC_VAL_THRESHOLD)) -> mc_count2' = 0
                  [] (numActive=3 /\ (isolated1'=TRUE \/ isolated2'=TRUE \/ isolated3'=TRUE)) -> (mc_count2'=0)
                  [] (numActive=2 /\ isolated2=TRUE /\ abs(sensor1.signal' - sensor3.signal') > MC_VAL_THRESHOLD /\ mc_count2 < MC_PERSISTENCE) -> (mc_count2' = mc_count2+1)
                  [] (numActive=2 /\ isolated2=TRUE /\ abs(sensor1.signal' - sensor3.signal') =< MC_VAL_THRESHOLD) -> (mc_count2' = 0)
                  [] OTHER -> UNCHANGED mc_count2
                  
next_mc_count3 == CASE ((numActive=3 /\ abs(sensor3.signal' - sensor2.signal') > MC_VAL_THRESHOLD /\ abs(sensor1.signal' - sensor3.signal') > MC_VAL_THRESHOLD /\ mc_count3 < MC_PERSISTENCE)) -> (mc_count3' = mc_count3 +1)
                  [] (numActive=3 /\ (abs(sensor3.signal' - sensor2.signal') > MC_VAL_THRESHOLD \/ abs(sensor1.signal' - sensor3.signal') > MC_VAL_THRESHOLD)) -> mc_count3' = 0
                  [] (numActive=3 /\ (isolated1'=TRUE \/ isolated2'=TRUE \/ isolated3'=TRUE)) -> (mc_count3'=0)
                  [] (numActive=2 /\ isolated3=TRUE /\ abs(sensor2.signal' - sensor1.signal') > MC_VAL_THRESHOLD /\ mc_count3 < MC_PERSISTENCE) -> (mc_count3' = mc_count3+1)
                  [] (numActive=2 /\ isolated3=TRUE /\ abs(sensor2.signal' - sensor1.signal') =< MC_VAL_THRESHOLD) -> (mc_count3' = 0)
                  [] OTHER -> UNCHANGED mc_count3
            
           

                 
\*calculating outputValid

outputValid_cal == CASE numActive'=3 -> outputValid'=TRUE
                   []   numActive'=2 /\ (mc_count1' < MC_PERSISTENCE) /\ (mc_count2' < MC_PERSISTENCE) /\ (mc_count3' < MC_PERSISTENCE) -> outputValid'=TRUE
                   []   numActive'=2 /\ ((mc_count1' < MC_PERSISTENCE) \/ (mc_count2' < MC_PERSISTENCE) \/ (mc_count3' < MC_PERSISTENCE)) ->outputValid'=FALSE
                   []   numActive'=1 -> outputValid'=TRUE
                   []   numActive'=0 -> outputValid'=FALSE
                 

invar1 == ~((isolated1'=FALSE) /\ (fault1'#0) /\ (isolated2'=FALSE) /\ (fault2'#0))

invar2 == ~((isolated2'=FALSE) /\ (fault2'#0) /\ (isolated3'=FALSE) /\ (fault3'#0))

invar3 == ~((isolated1'=FALSE) /\ (fault1'#0) /\ (isolated3'=FALSE) /\ (fault3'#0))

invariants == invar1 /\ invar2 /\ invar3

next == next_world_val /\ (noise1 \in -1..1) /\ (noise2 \in -1..1) /\ (noise3 \in -1..1) /\ (fault1 \in 0..2) /\ (fault2 \in 0..2) /\ (fault3 \in 0..2) /\ next_isolated1 /\ next_isolated2 /\ next_isolated3 /\ next_hw_count1 /\ next_hw_count2 /\ next_hw_count3 /\ next_mc_count1 /\ next_mc_count2 /\ next_mc_count3 /\ numActive_cal /\ outputValid_cal /\ invariants
=============================================================================
\* Modification History
\* Last modified Sat Mar 25 10:42:21 IST 2023 by 112102006
\* Created Thu Feb 02 20:09:21 IST 2023 by 112102006


=============================================================================
\* Modification History
\* Created Fri Mar 24 09:29:13 IST 2023 by 112102006


=============================================================================
\* Modification History
\* Created Fri Mar 24 10:26:19 IST 2023 by 112102006
