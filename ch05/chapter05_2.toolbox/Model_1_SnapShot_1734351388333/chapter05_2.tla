---------------------------- MODULE chapter05_2 ----------------------------

EXTENDS Integers
CONSTANT ResourceCap, MaxConsumerReq, Actors

ASSUME ResourceCap > 0
ASSUME MaxConsumerReq \in 1..ResourceCap
ASSUME Actors /= {}

(*--algorithm cache
variables resources_left = ResourceCap;

define 
    ResourceInvariant == resources_left >= 0
end define;

process actor \in Actors
variables 
    resources_needed \in 1..MaxConsumerReq
begin
    WaitForResources:
        while TRUE do
            await resources_left >= resources_needed;
            resources_left := resources_left - resources_needed;
        end while;
end process;

process time = "time"
begin
    Tick:
        resources_left := ResourceCap;
        goto Tick;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "2b1de8c1" /\ chksum(tla) = "1b22f979")
VARIABLES pc, resources_left

(* define statement *)
ResourceInvariant == resources_left >= 0

VARIABLE resources_needed

vars == << pc, resources_left, resources_needed >>

ProcSet == (Actors) \cup {"time"}

Init == (* Global variables *)
        /\ resources_left = ResourceCap
        (* Process actor *)
        /\ resources_needed \in [Actors -> 1..MaxConsumerReq]
        /\ pc = [self \in ProcSet |-> CASE self \in Actors -> "WaitForResources"
                                        [] self = "time" -> "Tick"]

WaitForResources(self) == /\ pc[self] = "WaitForResources"
                          /\ resources_left >= resources_needed[self]
                          /\ resources_left' = resources_left - resources_needed[self]
                          /\ pc' = [pc EXCEPT ![self] = "WaitForResources"]
                          /\ UNCHANGED resources_needed

actor(self) == WaitForResources(self)

Tick == /\ pc["time"] = "Tick"
        /\ resources_left' = ResourceCap
        /\ pc' = [pc EXCEPT !["time"] = "Tick"]
        /\ UNCHANGED resources_needed

time == Tick

Next == time
           \/ (\E self \in Actors: actor(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Mon Dec 16 13:16:22 CET 2024 by duke-deuce
\* Created Mon Dec 16 12:19:10 CET 2024 by duke-deuce
