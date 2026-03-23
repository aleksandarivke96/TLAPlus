----------------------------- MODULE OutboxPattern -----------------------------
EXTENDS Naturals

\* Set of business entities (e.g. order IDs) provided by a TLC model value.
CONSTANT Orders

VARIABLES db, outbox, broker, sent, acked, allMsgs, nextMsgId

vars == <<db, outbox, broker, sent, acked, allMsgs, nextMsgId>>

Message(id, ord) == [id |-> id, order |-> ord]

Init ==
    /\ db = [o \in Orders |-> "NEW"]
    /\ outbox = {}
    /\ broker = {}
    /\ sent = {}
    /\ acked = {}
    /\ allMsgs = {}
    /\ nextMsgId = 1

\* Atomic business transaction:
\* write DB state + write outbox message in one step.
CreateOrder(o) ==
    LET m == Message(nextMsgId, o) IN
    /\ db[o] = "NEW"
    /\ db' = [db EXCEPT ![o] = "CREATED"]
    /\ outbox' = outbox \cup {m}
    /\ allMsgs' = allMsgs \cup {m}
    /\ nextMsgId' = nextMsgId + 1
    /\ UNCHANGED <<broker, sent, acked>>

\* Relay publishes an outbox message to broker.
\* We keep outbox entry until broker ack is recorded.
RelaySend(m) ==
    /\ m \in outbox
    /\ broker' = broker \cup {m}
    /\ sent' = sent \cup {m.id}
    /\ UNCHANGED <<db, outbox, acked, allMsgs, nextMsgId>>

\* Broker confirms it has accepted the message.
AckFromBroker(m) ==
    /\ m \in broker
    /\ acked' = acked \cup {m.id}
    /\ UNCHANGED <<db, outbox, broker, sent, allMsgs, nextMsgId>>

\* Outbox cleanup happens only after ack.
CleanupOutbox(m) ==
    /\ m \in outbox
    /\ m.id \in acked
    /\ outbox' = outbox \ {m}
    /\ UNCHANGED <<db, broker, sent, acked, allMsgs, nextMsgId>>

Next ==
    \/ \E o \in Orders: CreateOrder(o)
    \/ \E m \in outbox: RelaySend(m)
    \/ \E m \in broker: AckFromBroker(m)
    \/ \E m \in outbox: CleanupOutbox(m)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ db \in [Orders -> {"NEW", "CREATED"}]
    /\ outbox \subseteq allMsgs
    /\ broker \subseteq allMsgs
    /\ sent \subseteq Nat
    /\ acked \subseteq Nat
    /\ nextMsgId \in Nat \ {0}

\* No acknowledged message can appear out of thin air.
AckedWereCreated ==
    \A id \in acked: \E m \in allMsgs: m.id = id

\* If order is created, then the corresponding outbox message existed at least once.
CreatedOrderHasMessage ==
    \A o \in Orders:
        db[o] = "CREATED" =>
            \E m \in allMsgs: m.order = o

Safety ==
    TypeOK /\ AckedWereCreated /\ CreatedOrderHasMessage

===============================================================================
