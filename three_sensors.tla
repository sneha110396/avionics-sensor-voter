--------------------------- MODULE three_sensors ---------------------------
EXTENDS Integers, realWorld, sensors
CONSTANTS HW_PERSISTENCE, MC_PERSISTENCE, MC_VAL_THRESHOLD
VARIABLES hw_count1, hw_count2, hw_count3, mc_count1, mc_count2, mc_count3, mc_next, isolated1, isolated2, isolated3

sensor1 == INSTANCE sensors
sensor2 == INSTANCE sensors
sensor3 == INSTANCE sensors

\*numActive == CASE [](isolated1=FALSE /\ isolated2=FALSE /\ isolated3=FALSE) -> 3
  \*          [](isolated1=TRUE /\ isolated2=FALSE /\ isolated3=FALSE) \/ (isolated1=FALSE /\ isolated2=TRUE /\ isolated3=FALSE) \/ (isolated1=FALSE /\ isolated2=FALSE /\ isolated3=TRUE) -> 2
    \*        [](isolated1=TRUE /\ isolated2=TRUE /\ isolated3=FALSE) \/ (isolated1=FALSE /\ isolated2=TRUE /\ isolated3=TRUE) \/ (isolated1=TRUE /\ isolated2=FALSE /\ isolated3=TRUE) -> 1
      \*      []OTHER ->0


reset_hw_count1 == IF (isolated1=FALSE /\ sensor1.hw_valid=TRUE)
                   THEN hw_count1=0
                   ELSE TRUE
reset_hw_count2 == IF (isolated2=FALSE /\ sensor2.hw_valid=TRUE)
                   THEN hw_count2=0
                   ELSE TRUE
reset_hw_count3 == IF (isolated3=FALSE /\ sensor3.hw_valid=TRUE)
                   THEN hw_count3=0
                   ELSE TRUE
                   
NoErrProceed == reset_hw_count1 \/ reset_hw_count2 \/ reset_hw_count3

=============================================================================
\* Modification History
\* Last modified Sun Feb 19 19:16:55 IST 2023 by 112102006
\* Created Thu Feb 02 20:09:21 IST 2023 by 112102006
