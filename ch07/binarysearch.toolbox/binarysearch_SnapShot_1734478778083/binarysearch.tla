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
        ELSE 2*f[x-1]
    IN f[n]

MaxInt == 4
(*--algorithm binary_search                  
variables low = 1,
          seq \in OrderedSeqOf(1..MaxInt, MaxInt),
          high = Len(seq),
          target \in 1..MaxInt,
          found_index = 0,
          counter = 0;
begin
Search:
  while low <= high do
    counter := counter + 1;
    with
      m = (high + low) \div 2
    do
        if seq[m] = target then
            found_index := m;
            goto Result;
        elsif seq[m] < target then
            low := m + 1;
        else
            high := m - 1;
        end if;
    end with;

  end while;
                  
  Result:
    if Len(seq) > 0 then
      assert Pow2(counter-1) <= Len(seq);
    end if;
    if target \in PT!Range(seq) then
      assert seq[found_index] = target;
    else
      assert found_index = 0;
    end if;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "d3096f28" /\ chksum(tla) = "2c289dc5")
VARIABLES pc, low, seq, high, target, found_index, counter

vars == << pc, low, seq, high, target, found_index, counter >>

Init == (* Global variables *)
        /\ low = 1
        /\ seq \in OrderedSeqOf(1..MaxInt, MaxInt)
        /\ high = Len(seq)
        /\ target \in 1..MaxInt
        /\ found_index = 0
        /\ counter = 0
        /\ pc = "Search"

Search == /\ pc = "Search"
          /\ IF low <= high
                THEN /\ counter' = counter + 1
                     /\ LET m == (high + low) \div 2 IN
                          IF seq[m] = target
                             THEN /\ found_index' = m
                                  /\ pc' = "Result"
                                  /\ UNCHANGED << low, high >>
                             ELSE /\ IF seq[m] < target
                                        THEN /\ low' = m + 1
                                             /\ high' = high
                                        ELSE /\ high' = m - 1
                                             /\ low' = low
                                  /\ pc' = "Search"
                                  /\ UNCHANGED found_index
                ELSE /\ pc' = "Result"
                     /\ UNCHANGED << low, high, found_index, counter >>
          /\ UNCHANGED << seq, target >>

Result == /\ pc = "Result"
          /\ IF Len(seq) > 0
                THEN /\ Assert(Pow2(counter-1) <= Len(seq), 
                               "Failure of assertion at line 46, column 7.")
                ELSE /\ TRUE
          /\ IF target \in PT!Range(seq)
                THEN /\ Assert(seq[found_index] = target, 
                               "Failure of assertion at line 49, column 7.")
                ELSE /\ Assert(found_index = 0, 
                               "Failure of assertion at line 51, column 7.")
          /\ pc' = "Done"
          /\ UNCHANGED << low, seq, high, target, found_index, counter >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Search \/ Result
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Wed Dec 18 00:39:08 CET 2024 by duke-deuce
\* Created Tue Dec 17 23:49:28 CET 2024 by duke-deuce
