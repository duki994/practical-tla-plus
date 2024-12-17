---------------------------- MODULE binarysearch ----------------------------
EXTENDS Sequences, Integers, TLC
PT == INSTANCE PT

OrderedSeqOf(set, n) ==
    {seq \in PT!SeqOf(set, n):
        \A x \in 2..Len(seq): \* just filter out unordered ones from all SeqOf combinations
            seq[x] <= seq[x-1] }
            
Pow2(n) ==
    LET f[x \in 0..n] ==
        IF x = 0
        THEN 1
        ELSE 2 * f[x - 1]
    IN f[n]

MaxInt == 4
(*--algorithm binarysearch
variables 
    i = 1,
    seq \in OrderedSeqOf(1..MaxInt, MaxInt),
    target \in 1..MaxInt,
    found_index = 0,
    counter = 0;
    
begin
    Search:
        while i <= Len(seq) do
            counter := counter + 1;
            if seq[i] = target then
                found_index := i;
                goto Result;
            else
                i := i + 1;
            end if;
        end while;
    Result:
        if Len(seq) > 0 then
            assert Pow2(counter-1) <= Len(seq)
        end if;
        if target \in PT!Range(seq) then
            assert seq[found_index] = target
        else 
            assert found_index = 0; \* 0 is out of DOMAIN seq
        end if;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "8d02d68" /\ chksum(tla) = "ec875da4")
VARIABLES pc, i, seq, target, found_index, counter

vars == << pc, i, seq, target, found_index, counter >>

Init == (* Global variables *)
        /\ i = 1
        /\ seq \in OrderedSeqOf(1..MaxInt, MaxInt)
        /\ target \in 1..MaxInt
        /\ found_index = 0
        /\ counter = 0
        /\ pc = "Search"

Search == /\ pc = "Search"
          /\ IF i <= Len(seq)
                THEN /\ counter' = counter + 1
                     /\ IF seq[i] = target
                           THEN /\ found_index' = i
                                /\ pc' = "Result"
                                /\ i' = i
                           ELSE /\ i' = i + 1
                                /\ pc' = "Search"
                                /\ UNCHANGED found_index
                ELSE /\ pc' = "Result"
                     /\ UNCHANGED << i, found_index, counter >>
          /\ UNCHANGED << seq, target >>

Result == /\ pc = "Result"
          /\ IF Len(seq) > 0
                THEN /\ Assert(Pow2(counter-1) <= Len(seq), 
                               "Failure of assertion at line 39, column 13.")
                ELSE /\ TRUE
          /\ IF target \in PT!Range(seq)
                THEN /\ Assert(seq[found_index] = target, 
                               "Failure of assertion at line 42, column 13.")
                ELSE /\ Assert(found_index = 0, 
                               "Failure of assertion at line 44, column 13.")
          /\ pc' = "Done"
          /\ UNCHANGED << i, seq, target, found_index, counter >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Search \/ Result
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Wed Dec 18 00:23:50 CET 2024 by duke-deuce
\* Created Tue Dec 17 23:49:28 CET 2024 by duke-deuce
