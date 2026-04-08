---- MODULE MutualExclusion ----
EXTENDS Naturals

CONSTANT N
ASSUME N \in Nat /\ N > 0

Procs == 1..N

VARIABLE state

States == {"idle", "trying", "critical"}

Init == state = [p \in Procs |-> "idle"]

TryEnter(p) ==
    /\ state[p] = "idle"
    /\ state' = [state EXCEPT ![p] = "trying"]

Enter(p) ==
    /\ state[p] = "trying"
    /\ \A q \in Procs : q # p => state[q] # "critical"
    /\ state' = [state EXCEPT ![p] = "critical"]

Exit(p) ==
    /\ state[p] = "critical"
    /\ state' = [state EXCEPT ![p] = "idle"]

Next == \E p \in Procs : TryEnter(p) \/ Enter(p) \/ Exit(p)

Spec == Init /\ [][Next]_state

TypeInvariant == \A p \in Procs : state[p] \in States

MutualExclusion == \A p, q \in Procs : p # q => ~(state[p] = "critical" /\ state[q] = "critical")
====