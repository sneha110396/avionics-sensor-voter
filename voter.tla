------------------------------- MODULE voter -------------------------------

EXTENDS Integers, TLC, Sequences
CONSTANTS HW_PERSISTENCE, MC_PERSISTENCE, MC_VAL_THRESHOLD, MAX_VAL, MIN_VAL
VARIABLES world_val, noise1, noise2, noise3, fault1, fault2, fault3, signal1, signal2, signal3, hw_valid1, hw_valid2, hw_valid3, numActive, outputValid, hw_count1, hw_count2, hw_count3, mc_count1, mc_count2, mc_count3, isolated1, isolated2, isolated3 

isolated == <<isolated1, isolated2, isolated3>>
hw_count == <<hw_count1, hw_count2, hw_count3>>
mc_count == <<mc_count1, mc_count2, mc_count3>>
fault == <<fault1, fault2, fault3>>
noise == <<noise1, noise2, noise3>>

\* calculating world_val
\* world_val can range from MIN_VAL to MAX_VAL

next_world_val == world_val' \in MIN_VAL..MAX_VAL
   
\* function to calculate signal from world_val and noise
\* If the signal value exceeds the MAX_VAL, we will set the signal value as MAX_VAL
\* If signal value becomes less than MIN_VAL, we will set the signal value as MIN_VAL

sig_w_noise(nois, wrld, max) == CASE (wrld + nois) > max -> max
           []   (wrld + nois) < -max -> -max
           [] OTHER -> wrld + nois

\* function to calculate absolute value

abs(x) == IF x>0 THEN x ELSE -x

\* initial conditions

init_noises == (noise1 \in -1..1) /\ (noise2 \in -1..1) /\ (noise3 \in -1..1)
init_faults == (fault1=0) /\ (fault2=0) /\ (fault3=0)
init_hw_valid == (hw_valid1=TRUE) /\ (hw_valid2=TRUE) /\ (hw_valid3=TRUE)
init_signal == (signal1=sig_w_noise(noise1, world_val, MAX_VAL)) /\ (signal2=sig_w_noise(noise2, world_val, MAX_VAL)) /\ (signal3=sig_w_noise(noise3, world_val, MAX_VAL))
init_hw_counts == (hw_count1=0) /\ (hw_count2=0) /\ (hw_count3=0)
init_mc_counts == (mc_count1=0) /\ (mc_count2=0) /\ (mc_count3=0)
init_isolated == (isolated1=FALSE) /\ (isolated2=FALSE) /\ (isolated3=FALSE)

init ==  /\ (world_val \in MIN_VAL..MAX_VAL) 
         /\ init_noises 
         /\ init_faults 
         /\ init_signal
         /\ init_hw_valid
         /\ init_hw_counts 
         /\ init_mc_counts 
         /\ init_isolated 
         /\ (numActive=3) 
         /\ (outputValid=TRUE)

\* function to calculate signal
\* If fault is 0, signal value will be realWorld value + noise
\* If fault is not 0, signal can take any arbitrary value between MAX_VAL and MIN_VAL

next_signal == /\ IF fault1=0 THEN signal1' = sig_w_noise(noise1, world_val, MAX_VAL) ELSE signal1' \in (MIN_VAL..MAX_VAL)
               /\ IF fault2=0 THEN signal2' = sig_w_noise(noise2, world_val, MAX_VAL) ELSE signal2' \in (MIN_VAL..MAX_VAL)
               /\ IF fault3=0 THEN signal3' = sig_w_noise(noise3, world_val, MAX_VAL) ELSE signal3' \in (MIN_VAL..MAX_VAL)

\* function to calculate hw_valid
\* hw_valid will take any arbitraey boolean value
\* If fault = 0, hw_valid will be TRUE

next_hw_valid == /\ IF fault1=0 THEN hw_valid1' = TRUE ELSE hw_valid1' \in {TRUE, FALSE}
                 /\ IF fault2=0 THEN hw_valid2' = TRUE ELSE hw_valid2' \in {TRUE, FALSE}
                 /\ IF fault3=0 THEN hw_valid3' = TRUE ELSE hw_valid3' \in {TRUE, FALSE}

\*creating sensors

sensor1 == [signal |-> signal1 , hw_valid |-> hw_valid1]
sensor2 == [signal |-> signal2 , hw_valid |-> hw_valid2]
sensor3 == [signal |-> signal3 , hw_valid |-> hw_valid3]

\* calculating isolated1, isolated2, isolated3
\* sensor can be isolated if it's hw_count reaches persistence
\* sensor can be isolated if it's miscompare count reaches persistence and there are already three valid sensors

new_isolated == [i \in 1..3 |-> ((hw_count[i]=HW_PERSISTENCE) \/ (numActive=3) \/ (mc_count[i]=MC_PERSISTENCE) \/ (isolated[i]=TRUE))]

next_isolated == (isolated1' = new_isolated[1]) /\ (isolated2' = new_isolated[2]) /\ (isolated3' = new_isolated[3]) 
           

\* calculating numActive
\* It calculates the number of active sensors at each step 

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

\* calculating hardware counts
\* If hardware flag of some sensor if FALSE, then hardware count will increase by one, provided it is less than the persistence level
\* If hardware count reaches the persistence level, it's value stays in persistence
    

next_hw_count_func(hw_vld, hw_cnt) == CASE (hw_vld' = FALSE \/ hw_cnt < HW_PERSISTENCE) -> (hw_cnt+1)
                                      [] (hw_vld'=TRUE) -> 0
                                      [] (hw_vld=HW_PERSISTENCE) -> HW_PERSISTENCE
                                      [] OTHER -> hw_cnt


next_hw_count == /\ (hw_count1'= next_hw_count_func(sensor1.hw_valid, hw_count1))
                 /\ (hw_count2'= next_hw_count_func(sensor2.hw_valid, hw_count2))
                 /\ (hw_count3'= next_hw_count_func(sensor3.hw_valid, hw_count3))




\* calculating miscompare counts

\* Two sensors are said to miscompare if the absolute difference between their signal values if greater than threshold

miscompare(i,j) == abs(i.signal' - j.signal') > MC_VAL_THRESHOLD

\* When there are three active sensors, miscompare count will increase by one if the respective sensor is miscomparing
\* When there are two active sensors and the respective sensor is isolated, it will count the miscompare between the other two sensors
\* For example, if sensor1 is isolated, mc_count1 will start counting the miscompare between sensor2 and sensor3
   
next_mc_count_func(numActv, snsr, other_snsr1, other_snsr2, mc_cnt, isoltd) == 
                        CASE (numActv=3 /\ miscompare(snsr, other_snsr1) /\ miscompare(snsr, other_snsr2) /\ mc_cnt < MC_PERSISTENCE) -> mc_cnt +1
                        [] (numActv=3 /\ ((~miscompare(snsr, other_snsr1)) \/ (~miscompare(snsr, other_snsr2)))) -> 0
                        [] (numActv=3 /\ (isolated1'=TRUE \/ isolated2'=TRUE \/ isolated3'=TRUE)) -> 0
                        [] (numActv=2 /\ isoltd=TRUE /\ miscompare(other_snsr1, other_snsr2) /\ mc_cnt < MC_PERSISTENCE) -> mc_cnt+1
                        [] (numActv=2 /\ isoltd=TRUE /\ (~miscompare(other_snsr1, other_snsr2))) -> 0
                        [] OTHER ->  mc_cnt
                                 
next_mc_count == /\ (mc_count1' = next_mc_count_func(numActive, sensor1, sensor2, sensor3, mc_count1, isolated1))
                 /\ (mc_count2' = next_mc_count_func(numActive, sensor2, sensor1, sensor3, mc_count2, isolated2))
                 /\ (mc_count3' = next_mc_count_func(numActive, sensor3, sensor2, sensor1, mc_count3, isolated3))

                 
\* calculating outputValid
\* When there are three active sensors, output will be valid
\* When there are two active sensors and one of the miscompare counts has reached threshold, then output is not valid
\* When there are two active sensors and all the miscompare counts are less than threshold, then output is valid
\* If there are one active sensor, output is valid
\* If there are no active sensors, output is not valid 

all_mc_counts_lt_persist == (mc_count1' < MC_PERSISTENCE) /\ (mc_count2' < MC_PERSISTENCE) /\ (mc_count3' < MC_PERSISTENCE)

next_outputValid == CASE numActive'=3 -> outputValid'=TRUE
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
        /\ next_signal
        /\ next_hw_valid 
        /\ next_isolated 
        /\ next_hw_count 
        /\ next_mc_count 
        /\ next_numActive 
        /\ next_outputValid 
        /\ invariants
        
hw_fault == (hw_count[1] = HW_PERSISTENCE) \/ (hw_count[2] = HW_PERSISTENCE) \/ (hw_count[3] = HW_PERSISTENCE) 

mc_fault == (mc_count[1] = MC_PERSISTENCE) \/ (mc_count[2] = MC_PERSISTENCE) \/ (mc_count[3] = MC_PERSISTENCE)

=============================================================================
\* Modification History
\* Last modified Tue May 02 17:24:40 IST 2023 by sumi1
\* Last modified Tue Apr 25 10:30:07 IST 2023 by 112102006
\* Created Thu Feb 02 20:09:21 IST 2023 by 112102006


=============================================================================
\* Modification History
\* Created Fri Mar 24 09:29:13 IST 2023 by 112102006


=============================================================================
\* Modification History
\* Created Fri Mar 24 10:26:19 IST 2023 by 112102006
