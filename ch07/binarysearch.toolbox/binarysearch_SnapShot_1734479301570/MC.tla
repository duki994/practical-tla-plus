---- MODULE MC ----
EXTENDS binarysearch, TLC

\* INIT definition @modelBehaviorNoSpec:0
init_17344792995506000 ==
FALSE/\low = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_17344792995507000 ==
FALSE/\low' = low
----
=============================================================================
\* Modification History
\* Created Wed Dec 18 00:48:19 CET 2024 by duke-deuce
