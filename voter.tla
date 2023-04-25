------------------------------- MODULE voter -------------------------------

EXTENDS Integers, TLC, Sequences
CONSTANTS HW_PERSISTENCE, MC_PERSISTENCE, MC_VAL_THRESHOLD, MAX_VAL, MIN_VAL
VARIABLES world_val, noise1, noise2, noise3, fault1, fault2, fault3, numActive, outputValid, hw_count1, hw_count2, hw_count3, mc_count1, mc_count2, mc_count3, isolated1, isolated2, isolated3 

isolated == <<isolated1, isolated2, isolated3>>
hw_count == <<hw_count1, hw_count2, hw_count3>>
mc_count == <<mc_count1, mc_count2, mc_count3>>
fault == <<fault1, fault2, fault3>>
noise == <<noise1, noise2, noise3>>

init_noises == (noise1 \in -1..1) /\ (noise2 \in -1..1) /\ (noise3 \in -1..1)
init_faults == (fault1=0) /\ (fault2=0) /\ (fault3=0)
init_hw_counts == (hw_count1=0) /\ (hw_count2=0) /\ (hw_count3=0)
init_mc_counts == (mc_count1=0) /\ (mc_count2=0) /\ (mc_count3=0)
init_isolated == (isolated1=FALSE) /\ (isolated2=FALSE) /\ (isolated3=FALSE)

init ==  /\ (world_val \in MIN_VAL..MAX_VAL) 
         /\ init_noises 
         /\ init_faults 
         /\ init_hw_counts 
         /\ init_mc_counts 
         /\ init_isolated 
         /\ (numActive=3) 
         /\ (outputValid=TRUE)



\* calculating world_val
\* world_val can range from MIN_VAL to MAX_VAL
\* The value of world_val in each step will be in the range previous value-1 to previous value + 1

next_world_val == 
                  CASE world_val \in (MIN_VAL+1)..(MAX_VAL-1) -> world_val' \in (world_val-1)..(world_val+1)
                  [] (world_val = MAX_VAL) -> world_val' \in {world_val-1, world_val}
                  [] (world_val = MIN_VAL) -> world_val' \in {world_val+1, world_val}
                  [] OTHER -> UNCHANGED world_val

\* some useful functions

\* function to calculate signal from world_val and noise

sig_w_noise(n,w,m) == CASE (w+n) > m -> m
           []   (w+n) < -m -> -m
           [] OTHER -> w+n

\* function to calculate absolute value

abs(x) == IF x>0 THEN x ELSE -x

\*Creating sensors

\* function to calculate signal

signal_func(ns, flt, world, max) == IF flt=0 THEN sig_w_noise(ns, world, max) ELSE RandomElement(-max..max)

\* function to calculate hw_valid

hw_valid_func(flt) == IF flt=0 THEN TRUE ELSE RandomElement({TRUE, FALSE})

\* creating three sensors
\* each sensor has two components, signal and hw_valid

sensor == [i \in 1..3 |-> [signal |-> signal_func(noise[i], fault[i], world_val, MAX_VAL), hw_valid |-> hw_valid_func(fault[i])]]


\* calculating isolated1, isolated2, isolated3
\* sensor can be isolated if it's hw_count reaches persistence
\* sensor can be isolated if it's miscompare count reaches persistence and there are already three valid sensors

new_isolated == [i \in 1..3 |-> ((hw_count[i]=HW_PERSISTENCE) \/ (numActive=3) \/ (mc_count[i]=MC_PERSISTENCE) \/ (isolated[i]=TRUE))]

next_isolated == (isolated1' = new_isolated[1]) /\ (isolated2' = new_isolated[2]) /\ (isolated3' = new_isolated[3]) 
           

\*calculating numActive

all_isolated == (isolated1' /\ isolated2' /\ isolated3')
two_isolated == \/ (~isolated1' /\ isolated2' /\ isolated3')
                \/ (isolated1' /\ ~isolated2' /\ isolated3')
                \/ (isolated1' /\ isolated2' /\ ~isolated3')
one_isolated == \/ (isolated1' /\ ~isolated2' /\ ~isolated3')
                \/ (~isolated1' /\ isolated2' /\ ~isolated3')
                \/ (~isolated1' /\ ~isolated2' /\ isolated3')
none_isolated == (~isolated1' /\ ~isolated2' /\ ~isolated3')
                     
           

next_numActive == CASE none_isolated -> numActive'=3
                  []   one_isolated -> numActive'=2
                  []   two_isolated -> numActive'=1
                  []   all_isolated -> numActive'=0

\*calculating hardware counts

next_hw_count_func(hw_vld, hw_cnt) == CASE (hw_vld' = FALSE \/ hw_cnt < HW_PERSISTENCE) -> (hw_cnt+1)
                                      [] (hw_vld'=TRUE) -> 0
                                      [] (hw_vld=HW_PERSISTENCE) -> HW_PERSISTENCE
                                      [] OTHER -> hw_cnt


next_hw_count == /\ (hw_count1'= next_hw_count_func(sensor[1].hw_valid, hw_count1))
                 /\ (hw_count2'= next_hw_count_func(sensor[2].hw_valid, hw_count2))
                 /\ (hw_count3'= next_hw_count_func(sensor[3].hw_valid, hw_count3))




\*calculating miscompare counts

miscompare(i,j) == abs(i.signal' - j.signal') > MC_VAL_THRESHOLD

next_mc_count_func(numActv, snsr, other_snsr1, other_snsr2, mc_cnt, isoltd) == 
                        CASE (numActv=3 /\ miscompare(snsr, other_snsr1) /\ miscompare(snsr, other_snsr2) /\ mc_cnt < MC_PERSISTENCE) -> mc_cnt +1
                        [] (numActv=3 /\ (miscompare(snsr, other_snsr1) \/ miscompare(snsr, other_snsr2))) -> 0
                        [] (numActv=3 /\ (isolated1'=TRUE \/ isolated2'=TRUE \/ isolated3'=TRUE)) -> 0
                        [] (numActv=2 /\ isoltd=TRUE /\ miscompare(other_snsr1, other_snsr2) /\ mc_cnt < MC_PERSISTENCE) -> mc_cnt+1
                        [] (numActv=2 /\ isoltd=TRUE /\ (~miscompare(other_snsr1, other_snsr2))) -> 0
                        [] OTHER ->  mc_cnt
                                 
next_mc_count == /\ (mc_count1' = next_mc_count_func(numActive, sensor[1], sensor[2], sensor[3], mc_count1, isolated1))
                 /\ (mc_count2' = next_mc_count_func(numActive, sensor[2], sensor[1], sensor[3], mc_count2, isolated2))
                 /\ (mc_count3' = next_mc_count_func(numActive, sensor[3], sensor[2], sensor[1], mc_count3, isolated3))

                 
\*calculating outputValid

all_mc_counts_lt_persist == (mc_count1' < MC_PERSISTENCE) /\ (mc_count2' < MC_PERSISTENCE) /\ (mc_count3' < MC_PERSISTENCE)

outputValid_cal == CASE numActive'=3 -> outputValid'=TRUE
                   []   numActive'=2 /\ all_mc_counts_lt_persist -> outputValid'=TRUE
                   []   numActive'=2 /\ (~ all_mc_counts_lt_persist) -> outputValid'=FALSE
                   []   numActive'=1 -> outputValid'=TRUE
                   []   numActive'=0 -> outputValid'=FALSE
                 

invar1 == ~((isolated1'=FALSE) /\ (fault1'#0) /\ (isolated2'=FALSE) /\ (fault2'#0))

invar2 == ~((isolated2'=FALSE) /\ (fault2'#0) /\ (isolated3'=FALSE) /\ (fault3'#0))

invar3 == ~((isolated1'=FALSE) /\ (fault1'#0) /\ (isolated3'=FALSE) /\ (fault3'#0))

invariants == invar1 /\ invar2 /\ invar3

next_noises == (noise1' \in -1..1) /\ (noise2' \in -1..1) /\ (noise3' \in -1..1)
next_faults == (fault1' \in 0..2) /\ (fault2' \in 0..2) /\ (fault3' \in 0..2)

next == /\ next_world_val 
        /\ next_noises 
        /\ next_faults 
        /\ next_isolated 
        /\ next_hw_count 
        /\ next_mc_count 
        /\ next_numActive 
        /\ outputValid_cal 
        /\ invariants
=============================================================================
\* Modification History
\* Last modified Tue Apr 25 10:30:07 IST 2023 by 112102006
\* Last modified Tue Apr 25 08:19:29 IST 2023 by sumi1
\* Created Thu Feb 02 20:09:21 IST 2023 by 112102006


=============================================================================
\* Modification History
\* Created Fri Mar 24 09:29:13 IST 2023 by 112102006


=============================================================================
\* Modification History
\* Created Fri Mar 24 10:26:19 IST 2023 by 112102006
