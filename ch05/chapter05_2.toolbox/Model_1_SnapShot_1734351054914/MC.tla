---- MODULE MC ----
EXTENDS chapter05_2, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2
----

\* MV CONSTANT definitions Actors
const_173435105288817000 == 
{a1, a2}
----

\* CONSTANT definitions @modelParameterConstants:0ResourceCap
const_173435105288818000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:1MaxConsumerReq
const_173435105288819000 == 
2
----

=============================================================================
\* Modification History
\* Created Mon Dec 16 13:10:52 CET 2024 by duke-deuce
