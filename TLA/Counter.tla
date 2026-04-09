---- MODULE Counter ----
EXTENDS Naturals

VARIABLE counter

Init ==
    counter = 1

Next ==
    IF counter < 10
    THEN counter' = counter + 1
    ELSE counter' = counter

Spec ==
    Init /\ [][Next]_counter
====