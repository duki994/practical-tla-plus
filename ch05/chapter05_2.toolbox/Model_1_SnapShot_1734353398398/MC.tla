---- MODULE MC ----
EXTENDS chapter05_2, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2
----

\* MV CONSTANT definitions Actors
const_17343533960382000 == 
{a1, a2}
----

\* CONSTANT definitions @modelParameterConstants:0ResourceCap
const_17343533960383000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:1MaxConsumerReq
const_17343533960384000 == 
2
----

=============================================================================
\* Modification History
\* Created Mon Dec 16 13:49:56 CET 2024 by duke-deuce
