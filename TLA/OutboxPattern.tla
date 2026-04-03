---- MODULE OutboxPattern ----
EXTENDS Naturals

VARIABLES db, outbox, extSystem, nextMsgId

Orders == {"o1", "o2"}

Init ==
    /\ db         = [o \in Orders |-> "NEW"]
    /\ outbox     = {}
    /\ extSystem  = {}
    /\ nextMsgId  = 0

CreateOrder(o) ==
    LET msg == [id |-> nextMsgId, order |-> o] IN
    /\ db[o] = "NEW"
    /\ db'        = [db EXCEPT ![o] = "CREATED"]
    /\ outbox'    = outbox \cup {msg}
    /\ nextMsgId' = nextMsgId + 1
    /\ UNCHANGED extSystem

DeliverMessage(msg) ==
    /\ msg \in outbox
    /\ msg \notin extSystem
    /\ extSystem' = extSystem \cup {msg}
    /\ UNCHANGED <<db, outbox, nextMsgId>>

CleanupOutbox(msg) ==
    /\ msg \in outbox
    /\ msg \in extSystem
    /\ outbox' = outbox \ {msg}
    /\ UNCHANGED <<db, extSystem, nextMsgId>>

Next ==
    \/ \E o \in Orders      : CreateOrder(o)
    \/ \E msg \in outbox    : DeliverMessage(msg)
    \/ \E msg \in outbox    : CleanupOutbox(msg)

Spec == Init /\ [][Next]_<<db, outbox, extSystem, nextMsgId>>

TypeInvariant ==
    /\ db \in [Orders -> {"NEW", "CREATED"}]
    /\ \A msg \in outbox    : msg.id \in Nat
    /\ \A msg \in extSystem : msg.id \in Nat

Consistency ==
    \A msg \in extSystem : msg \in outbox \/ msg.order \in Orders
====
\end{lstlisting}