------------------------------ MODULE sensors ------------------------------
EXTENDS realWorld

fault == CHOOSE x \in 0..2 : TRUE

noise == CHOOSE x \in -1..1 : TRUE

f(n,w,m) == CASE (w+n) > m -> m
           []   (w+n) < -m -> -m
           [] OTHER -> w+n
           
signal == IF fault=0
          THEN f(noise, world_val, MAX_VAL)
          ELSE CHOOSE x \in MIN_VAL..MAX_VAL : TRUE
           

hw_valid == IF fault=0
            THEN TRUE
            ELSE CHOOSE x \in {TRUE, FALSE} : TRUE



=============================================================================
\* Modification History
\* Last modified Sun Feb 19 19:16:08 IST 2023 by 112102006
\* Created Thu Feb 02 21:42:32 IST 2023 by 112102006EXTENDS Integers, realWorld
