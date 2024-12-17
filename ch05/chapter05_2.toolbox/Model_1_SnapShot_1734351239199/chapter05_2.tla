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
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "63650aeb" /\ chksum(tla) = "be574569")
VARIABLE resources_left

(* define statement *)
ResourceInvariant == resources_left >= 0

VARIABLE resources_needed

vars == << resources_left, resources_needed >>

ProcSet == (Actors)

Init == (* Global variables *)
        /\ resources_left = ResourceCap
        (* Process actor *)
        /\ resources_needed \in [Actors -> 1..MaxConsumerReq]

actor(self) == /\ resources_left >= resources_needed[self]
               /\ resources_left' = resources_left - resources_needed[self]
               /\ UNCHANGED resources_needed

Next == (\E self \in Actors: actor(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Mon Dec 16 13:13:30 CET 2024 by duke-deuce
\* Created Mon Dec 16 12:19:10 CET 2024 by duke-deuce
