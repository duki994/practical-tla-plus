---------------------------- MODULE binarysearch ----------------------------
EXTENDS Sequences, Integers, TLC
PT == INSTANCE PT

OrderedSeqOf(set, n) ==
    {seq \in PT!SeqOf(set, n):
        \A x \in 2..Len(seq): \* just filter out unordered ones from all SeqOf combinations
            seq[x] <= seq[x-1] }
           
Range(f) == {f[x]: x \in DOMAIN f}
            
Pow2(n) ==
    LET f[x \in 0..n] ==
        IF x = 0
        THEN 1
        ELSE 2*f[x-1]
    IN f[n]

MaxInt == 4
(* --algorithm definitely_binary_search
variables low = 1,
          seq \in OrderedSeqOf(1..MaxInt, MaxInt),
          high = Len(seq),  
          target \in 1..MaxInt,
          counter = 0,
          found_index = 0;
begin
Search:
while low <= high do
    counter := counter + 1;
    with
      lh = high - low,
      m = high - (lh \div 2)
    do
      assert lh <= MaxInt;
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
    if target \in Range(seq) then
        assert seq[found_index] = target;
    else
        assert found_index = 0;
    end if;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "c6fbe963" /\ chksum(tla) = "167d8e8c")
VARIABLES pc, low, seq, high, target, counter, found_index

vars == << pc, low, seq, high, target, counter, found_index >>

Init == (* Global variables *)
        /\ low = 1
        /\ seq \in OrderedSeqOf(1..MaxInt, MaxInt)
        /\ high = Len(seq)
        /\ target \in 1..MaxInt
        /\ counter = 0
        /\ found_index = 0
        /\ pc = "Search"

Search == /\ pc = "Search"
          /\ IF low <= high
                THEN /\ counter' = counter + 1
                     /\ LET lh == high - low IN
                          LET m == high - (lh \div 2) IN
                            /\ Assert(lh <= MaxInt, 
                                      "Failure of assertion at line 35, column 7.")
                            /\ IF seq[m] = target
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
                     /\ UNCHANGED << low, high, counter, found_index >>
          /\ UNCHANGED << seq, target >>

Result == /\ pc = "Result"
          /\ IF Len(seq) > 0
                THEN /\ Assert(Pow2(counter-1) <= Len(seq), 
                               "Failure of assertion at line 48, column 7.")
                ELSE /\ TRUE
          /\ IF target \in Range(seq)
                THEN /\ Assert(seq[found_index] = target, 
                               "Failure of assertion at line 51, column 9.")
                ELSE /\ Assert(found_index = 0, 
                               "Failure of assertion at line 53, column 9.")
          /\ pc' = "Done"
          /\ UNCHANGED << low, seq, high, target, counter, found_index >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Search \/ Result
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Wed Dec 18 00:48:14 CET 2024 by duke-deuce
\* Created Tue Dec 17 23:49:28 CET 2024 by duke-deuce
