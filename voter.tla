------------------------------- MODULE voter -------------------------------

EXTENDS Integers, TLC, Sequences
CONSTANTS HW_PERSISTENCE, MC_PERSISTENCE, MC_VAL_THRESHOLD, MAX_VAL, MIN_VAL
VARIABLES world_val, noise1, noise2, noise3, fault1, fault2, fault3, numActive, outputValid, hw_count1, hw_count2, hw_count3, mc_count1, mc_count2, mc_count3, isolated1, isolated2, isolated3 

isolated == <<isolated1, isolated2, isolated3>>
hw_count == <<hw_count1, hw_count2, hw_count3>>
mc_count == <<mc_count1, mc_count2, mc_count3>>

init == (world_val \in MIN_VAL..MAX_VAL) /\ (noise1 \in -1..1) /\ (noise2 \in -1..1) /\ (noise3 \in -1..1) /\ (fault1=0) /\ (fault2=0) /\ (fault3=0) /\ (hw_count1=0) /\ (hw_count2=0) /\ (hw_count3=0) /\ (mc_count1=0) /\ (mc_count2=0) /\ (mc_count3=0) /\ (isolated1=FALSE) /\ (isolated2=FALSE) /\ (isolated3=FALSE) /\ (numActive=3) /\ (outputValid=TRUE)



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

fault == <<fault1, fault2, fault3>>

noise == <<noise1, noise2, noise3>>

sensor == [i \in 1..3 |-> [signal |-> signal_func(noise[i], fault[i], world_val, MAX_VAL), hw_valid |-> hw_valid_func(fault[i])]]


\*calculating isolated1, isolated2, isolated3

next_isolated == [i \in 1..3 |-> IF ((hw_count[i]=HW_PERSISTENCE) \/ (numActive=3 \/ mc_count[i]=MC_PERSISTENCE)) \/ (isolated[i]=TRUE)
                                 THEN isolated[i]' = TRUE 
                                 ELSE isolated[i]' = FALSE]


              

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

next_hw_count == [i \in 1..3 |-> CASE (sensor[i].hw_valid' = FALSE \/ hw_count[i] < HW_PERSISTENCE) -> (hw_count[i]' = hw_count[i]+1)
                                 [] (sensor[i].hw_valid'=TRUE) -> (hw_count[i]' = 0)
                                 [] (hw_count[i]=HW_PERSISTENCE) -> (hw_count[i]'=HW_PERSISTENCE)
                                 [] OTHER -> UNCHANGED hw_count[i]]


\*calculating miscompare counts

next_mc_count == [i \in 1..3 |-> CASE ((numActive=3 /\ abs(sensor[i].signal' - sensor[(i % 3)+1].signal') > MC_VAL_THRESHOLD /\ abs(sensor[i].signal' - sensor[((i+1)%3)+1].signal') > MC_VAL_THRESHOLD /\ mc_count[i] < MC_PERSISTENCE)) -> (mc_count[i]' = mc_count[i] +1)
                                 [] (numActive=3 /\ (abs(sensor[i].signal' - sensor[(i%3)+1].signal') > MC_VAL_THRESHOLD \/ abs(sensor[i].signal' - sensor[((i+1)%3)+1].signal') > MC_VAL_THRESHOLD)) -> mc_count[i]' = 0
                                 [] (numActive=3 /\ (isolated1'=TRUE \/ isolated2'=TRUE \/ isolated3'=TRUE)) -> (mc_count[i]'=0)
                                 [] (numActive=2 /\ isolated[i]=TRUE /\ abs(sensor[(i%3)+1].signal' - sensor[((i+1)%3)+1].signal') > MC_VAL_THRESHOLD /\ mc_count[i] < MC_PERSISTENCE) -> (mc_count[i]' = mc_count[i]+1)
                                 [] (numActive=2 /\ isolated[i]=TRUE /\ abs(sensor[(i%3)+1].signal' - sensor[((i+1)%3)+1].signal') =< MC_VAL_THRESHOLD) -> (mc_count[i]' = 0)
                                 [] OTHER -> UNCHANGED mc_count[i]]

                 
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

next == next_world_val /\ (noise1' \in -1..1) /\ (noise2' \in -1..1) /\ (noise3' \in -1..1) /\ (fault1' \in 0..2) /\ (fault2' \in 0..2) /\ (fault3' \in 0..2) /\ next_isolated[1] /\ next_isolated[2] /\ next_isolated[3] /\ next_hw_count[1] /\ next_hw_count[2] /\ next_hw_count[3] /\ next_mc_count[1] /\ next_mc_count[2] /\ next_mc_count[3] /\ numActive_cal /\ outputValid_cal /\ invariants
=============================================================================
\* Modification History
\* Last modified Thu Mar 30 18:37:59 IST 2023 by 112102006
\* Created Thu Feb 02 20:09:21 IST 2023 by 112102006


=============================================================================
\* Modification History
\* Created Fri Mar 24 09:29:13 IST 2023 by 112102006


=============================================================================
\* Modification History
\* Created Fri Mar 24 10:26:19 IST 2023 by 112102006
