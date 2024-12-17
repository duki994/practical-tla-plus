------------------------------ MODULE leftpad ------------------------------
EXTENDS TLC, Sequences, Integers
PT == INSTANCE PT

Leftpad(c, n, str) ==
    LET
        outlength == PT!Max(Len(str), n)
        padlength == 
            CHOOSE padlength \in 0..n:
                padlength + Len(str) = outlength
    IN
        [x \in 1..padlength |-> c] \o str



=============================================================================
\* Modification History
\* Last modified Tue Dec 17 15:09:04 CET 2024 by Dusan
\* Created Tue Dec 17 15:05:43 CET 2024 by Dusan
