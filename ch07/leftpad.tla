------------------------------ MODULE leftpad ------------------------------
EXTENDS TLC, Sequences, Integers
PT == INSTANCE PT

Leftpad(c, n, str) ==
    IF n < 0 THEN str ELSE
    LET
        outlength == PT!Max(Len(str), n)
        padlength == CHOOSE padlength \in 0..n: 
            padlength + Len(str) = outlength
    IN
        [x \in 1..padlength |-> c] \o str
        

Characters == {"a", "b", "c"}

(*--algorithm leftpad
variables
    in_c \in Characters \union {" "},
    in_n \in 0..6,
    in_str \in PT!SeqOf(Characters, 6),
    output;
        
begin
    assert in_n >= 0;
    output := in_str;
    while Len(output) < in_n do
        output := <<in_c>> \o output
    end while;
    assert output = Leftpad(in_c, in_n, in_str);
end algorithm;*)        
\* BEGIN TRANSLATION (chksum(pcal) = "eb236b37" /\ chksum(tla) = "6c73379")
CONSTANT defaultInitValue
VARIABLES pc, in_c, in_n, in_str, output

vars == << pc, in_c, in_n, in_str, output >>

Init == (* Global variables *)
        /\ in_c \in (Characters \union {" "})
        /\ in_n \in 0..6
        /\ in_str \in PT!SeqOf(Characters, 6)
        /\ output = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(in_n >= 0, "Failure of assertion at line 25, column 5.")
         /\ output' = in_str
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << in_c, in_n, in_str >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF Len(output) < in_n
               THEN /\ output' = <<in_c>> \o output
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(output = Leftpad(in_c, in_n, in_str), 
                              "Failure of assertion at line 30, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED output
         /\ UNCHANGED << in_c, in_n, in_str >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 



=============================================================================
\* Modification History
\* Last modified Tue Dec 17 23:43:14 CET 2024 by duke-deuce
\* Last modified Tue Dec 17 15:09:04 CET 2024 by Dusan
\* Created Tue Dec 17 15:05:43 CET 2024 by Dusan
