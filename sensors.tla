------------------------------ MODULE sensors ------------------------------
EXTENDS Integers, realWorld
VARIABLES hw_valid, noise, fault

init_sensors == (hw_valid = TRUE) /\ (noise \in -1..1) /\ (fault=0)

invariant_sensors == (fault'=0) => (hw_valid'=TRUE)

next_sensors == (fault \in 0..2) /\ (noise \in -1..1) /\ (hw_valid \in {TRUE, FALSE}) /\  (fault' \in 0..2) /\ (noise' \in -1..1) /\ (hw_valid' \in {TRUE, FALSE}) /\ invariant_sensors



=============================================================================
\* Modification History
\* Last modified Thu Feb 02 22:35:13 IST 2023 by 112102006
\* Created Thu Feb 02 21:42:32 IST 2023 by 112102006
