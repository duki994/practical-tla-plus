---- MODULE MC ----
EXTENDS chapter05_2, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2
----

\* MV CONSTANT definitions Actors
const_173435295696029000 == 
{a1, a2}
----

\* CONSTANT definitions @modelParameterConstants:0ResourceCap
const_173435295696030000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:1MaxConsumerReq
const_173435295696031000 == 
2
----

=============================================================================
\* Modification History
\* Created Mon Dec 16 13:42:36 CET 2024 by duke-deuce
