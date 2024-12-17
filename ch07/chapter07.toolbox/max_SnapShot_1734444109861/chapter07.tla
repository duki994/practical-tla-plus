----------------------------- MODULE chapter07 -----------------------------
EXTENDS Integers, Sequences, TLC
CONSTANTS IntSet, MaxSeqLen

ASSUME IntSet \subseteq Int
ASSUME MaxSeqLen > 0
PT == INSTANCE PT
Max(seq) ==
    LET set == {seq[i]: i \in 1..Len(seq)}
    IN CHOOSE x \in set: \A y \in set: y <= x
    
AllInputs == PT!SeqOf(IntSet, MaxSeqLen)

(*--algorithm max
variables seq \in AllInputs, i = 1, max;
begin
    max := seq[i];
    while i <= Len(seq) do
        if max < seq[i] then
            max := seq[i]
        end if;
        i := i + 1;
    end while;
    assert max = Max(seq);
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "72076d31" /\ chksum(tla) = "bfba872f")
CONSTANT defaultInitValue
VARIABLES pc, seq, i, max

vars == << pc, seq, i, max >>

Init == (* Global variables *)
        /\ seq \in AllInputs
        /\ i = 1
        /\ max = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ max' = seq[i]
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << seq, i >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i <= Len(seq)
               THEN /\ IF max < seq[i]
                          THEN /\ max' = seq[i]
                          ELSE /\ TRUE
                               /\ max' = max
                    /\ i' = i + 1
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(max = Max(seq), 
                              "Failure of assertion at line 24, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << i, max >>
         /\ seq' = seq

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
    


=============================================================================
\* Modification History
\* Last modified Tue Dec 17 15:00:56 CET 2024 by Dusan
\* Created Tue Dec 17 14:08:40 CET 2024 by Dusan
