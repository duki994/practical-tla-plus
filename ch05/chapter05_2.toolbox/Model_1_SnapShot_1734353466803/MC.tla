---- MODULE MC ----
EXTENDS chapter05_2, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2
----

\* MV CONSTANT definitions Actors
const_17343534647736000 == 
{a1, a2}
----

\* CONSTANT definitions @modelParameterConstants:0ResourceCap
const_17343534647737000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:1MaxConsumerReq
const_17343534647738000 == 
2
----

=============================================================================
\* Modification History
\* Created Mon Dec 16 13:51:04 CET 2024 by duke-deuce
