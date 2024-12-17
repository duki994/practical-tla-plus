-------------------------- MODULE chapter06dekker --------------------------

EXTENDS TLC, Integers
CONSTANT Threads

(*--algorithm dekker
variables flag = [t \in Threads |-> FALSE];
fair process thread \in Threads
begin
    P1: flag[self] := TRUE;
    \* all threads except self are false
    P2: 
        while \E t \in Threads \ {self}: flag[t] do
            P2_1: flag[self] := FALSE;
            P2_2: flag[self] := TRUE;
        end while;
    CS: skip;
    P3: flag[self] := FALSE;
    P4: goto P1;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "cb2a128a" /\ chksum(tla) = "5955bdf0")
VARIABLES pc, flag

vars == << pc, flag >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ flag = [t \in Threads |-> FALSE]
        /\ pc = [self \in ProcSet |-> "P1"]

P1(self) == /\ pc[self] = "P1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "P2"]

P2(self) == /\ pc[self] = "P2"
            /\ IF \E t \in Threads \ {self}: flag[t]
                  THEN /\ pc' = [pc EXCEPT ![self] = "P2_1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "CS"]
            /\ flag' = flag

P2_1(self) == /\ pc[self] = "P2_1"
              /\ flag' = [flag EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "P2_2"]

P2_2(self) == /\ pc[self] = "P2_2"
              /\ flag' = [flag EXCEPT ![self] = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "P2"]

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "P3"]
            /\ flag' = flag

P3(self) == /\ pc[self] = "P3"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "P4"]

P4(self) == /\ pc[self] = "P4"
            /\ pc' = [pc EXCEPT ![self] = "P1"]
            /\ flag' = flag

thread(self) == P1(self) \/ P2(self) \/ P2_1(self) \/ P2_2(self)
                   \/ CS(self) \/ P3(self) \/ P4(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* for any two different threads, they can't both be in CS at the same time
AtMostOneCritical ==
    \A t1, t2 \in Threads:
        t1 /= t2 => ~(pc[t1] = "CS" /\ pc[t2] = "CS")

Liveness ==
    \A t \in Threads:
        <>(pc[t] = "CS")

=============================================================================
\* Modification History
\* Last modified Tue Dec 17 13:39:34 CET 2024 by Dusan
\* Created Tue Dec 17 12:58:29 CET 2024 by Dusan
