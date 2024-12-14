----------------------------- MODULE chapter05 -----------------------------

EXTENDS TLC, Integers, Sequences
CONSTANTS MaxQueueSize \* Defined in model as external param

(*--algorithm message_queue
variable queue = <<>>;

define
    BoundedQueue == Len(queue) <= MaxQueueSize
end define;

process writer = "writer"
begin Write:
    while TRUE do
        queue := Append(queue, "msg");
        await Len(queue) <= MaxQueueSize;
    end while;
end process;    

process reader = "reader"
variables current_message = "none"
begin Read:
    while TRUE do
        await queue /= <<>>;
        current_message := Head(queue);
        queue := Tail(queue);
    end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "c4107529" /\ chksum(tla) = "8c5057a2")
VARIABLE queue

(* define statement *)
BoundedQueue == Len(queue) <= MaxQueueSize

VARIABLE current_message

vars == << queue, current_message >>

ProcSet == {"writer"} \cup {"reader"}

Init == (* Global variables *)
        /\ queue = <<>>
        (* Process reader *)
        /\ current_message = "none"

writer == /\ queue' = Append(queue, "msg")
          /\ UNCHANGED current_message

reader == /\ current_message' = Head(queue)
          /\ queue' = Tail(queue)

Next == writer \/ reader

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Dec 13 16:56:16 CET 2024 by Dusan
\* Created Fri Dec 13 16:46:34 CET 2024 by Dusan
