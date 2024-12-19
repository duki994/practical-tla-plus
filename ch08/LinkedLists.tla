---------------------------- MODULE LinkedLists ----------------------------
CONSTANT NULL
LOCAL INSTANCE FiniteSets \* For Cardinality
LOCAL INSTANCE Sequences \* For len
LOCAL INSTANCE TLC \* For Assert
LOCAL INSTANCE Integers \* For a..b

LOCAL Range(f) == {f[x]: x \in DOMAIN f}
LOCAL PointerMaps(Nodes) == [Nodes -> Nodes \union {NULL}]

LOCAL isLinkedList(PointerMap) ==
    LET
        \* nodes are actually domain of PointerMap [a |-> b, b |-> c, c |-> a] etc.
        nodes = DOMAIN PointerMap
        all_seqs = [1..Cardinality(nodes) -> nodes] \* give me all possible sequences/orderings
    IN \E ordering \in all_seqs
        \* each node points to next node in ordering
        /\ \A i \in 1..Len(ordering)-1:
            PointerMap[ordering[i]] = ordering[i+1]
        \* all nodes in the mapping appear in the ordering
        /\ nodes \subseteq Range(ordering)
        


LinkedLists(Nodes) == 
    IF NULL \in Nodes THEN Assert(FALSE, "NULL cannot be in nodes") ELSE
    LET
        node_subsets == (SUBSET nodes \ {{}})
        pointer_maps_sets == {PointerMap(subn): subn \in node_subsets}
        \* pointer_maps_sets is a set of sets of functions
        \* so we need to union them all together
        all_pointer_maps == UNION pointer_maps_sets
    IN
        {pm \in all_pointer_maps: isLinkedList(pm)}
        

Ring(LL) == (DOMAIN LL = Range(LL))
First(LL) == 
    IF Ring(LL) 
    THEN CHOOSE node \in DOMAIN LL:
        TRUE
    ELSE CHOOSE node \in DOMAIN LL:
        node \notin Range(LL) 
        
Cyclic(LL) == NULL \notin Range(LL)



=============================================================================
\* Modification History
\* Last modified Thu Dec 19 23:43:35 CET 2024 by duke-deuce
\* Created Thu Dec 19 00:34:07 CET 2024 by duke-deuce
