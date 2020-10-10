-------------------------------- MODULE ping --------------------------------
EXTENDS Integers, Sequences

CONSTANTS Nodes

VARIABLES time,
          mq \* Messages queues where mq[<<a, b>>] is the sequence of messages sent from a to b.


Message == [ type: {"Ping", "Pong"}, nonce: Nat ]

TypeOK == /\ time \in Nat
          /\ mq \in [ k \in Nodes \X Nodes |-> Seq(Message) ]

SendPing(a, b, nonce) ==
    /\ mq' = [mq EXCEPT ![<<a, b>>] = <<[ type |-> "Ping", nonce |-> nonce ]>> \o @]
    /\ UNCHANGED time

RecvPing(a, b) ==
    /\ Len(mq[<<b, a>>]) > 0
    /\ Head(mq[<<b, a>>]).type = "Ping"
    /\ mq' = [mq EXCEPT
           ![<<a, b>>] = <<[ type |-> "Pong", nonce |-> Head(mq[<<b, a>>]).nonce ]>> \o @,
           ![<<b, a>>] = Tail(mq[<<b, a>>])
       ]
    /\ UNCHANGED time

RecvPong(a, b) ==
    /\ Len(mq[<<b, a>>]) > 0
    /\ Head(mq[<<b, a>>]).type = "Pong"
    /\ mq' = [mq EXCEPT
           ![<<b, a>>] = Tail(mq[<<b, a>>])
       ]
    /\ UNCHANGED time

Tick == /\ time' = time + 1
        /\ UNCHANGED mq

Init == /\ time = 0
        /\ mq = [ k \in Nodes \X Nodes |-> <<>> ]

Next ==  \/ Tick
         \/ \E a, b \in Nodes: a # b /\ SendPing(a, b, time)
         \/ \E a, b \in Nodes: RecvPing(a, b)
         \/ \E a, b \in Nodes: RecvPong(a, b)        

=============================================================================
\* Modification History
\* Last modified Sat Oct 10 11:37:16 CST 2020 by ian
\* Last modified Sat Oct 10 11:06:10 CST 2020 by ian
\* Created Thu Sep 24 02:57:30 PDT 2020 by ian
