----------------------------- MODULE chapter03 -----------------------------

EXTENDS TLC, Integers, Sequences

PT == INSTANCE PT

Capacity == 7
Items == {"a", "b", "c"}

HardcodedItemSet == [
    a |-> [size |-> 1, value |-> 1],
    b |-> [size |-> 2, value |-> 3],
    v |-> [size |-> 3, value |-> 1]
]

ItemParams == [size: 2..4, value: 0..5]
ItemSets == [Items -> ItemParams]

KnapsackSize(sack, itemset) ==
    LET size_for(item) == itemset[item].size * sack[item] \* actual size is (size of itemset item) * (item value for sack)
    IN PT!ReduceSet(LAMBDA item, acc: size_for(item) + acc, Items, 0)

ValidKnapsacks(itemset) ==
    {sack \in [Items -> 0..4]: KnapsackSize(sack, itemset) <= Capacity}
    
KnapsackValue(sack, itemset) ==
    LET value_for(item) == itemset[item].value * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: value_for(item) + acc, Items, 0)

BestKnapsacksOne(itemset) ==
    LET all == ValidKnapsacks(itemset)
    IN
        CHOOSE all_the_best \in SUBSET all:
            \E good \in all_the_best:
                /\ \A other \in all_the_best:
                    KnapsackValue(good, itemset) = KnapsackValue(other, itemset)
                /\ \A worse \in all \ all_the_best:
                    KnapsackValue(good, itemset) > KnapsackValue(worse, itemset)
                    

BestKnapsacksTwo(itemset) ==
    LET 
        value(sack) == KnapsackValue(sack, itemset)
        all == ValidKnapsacks(itemset)
        best == CHOOSE best \in all:
            \A worse \in all \ {best}:
                value(best) >= value(worse)
    IN
        {k \in all: value(best) = value(k)} 
            


=============================================================================
\* Modification History
\* Last modified Tue Dec 10 13:53:09 CET 2024 by Dusan
\* Created Tue Dec 10 11:52:05 CET 2024 by Dusan
