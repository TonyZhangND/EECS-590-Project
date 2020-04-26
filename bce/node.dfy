module BCE_Protocol_Node {

type symbol = nat
type syndrome = seq<bool>

datatype NodeState = Phase1 | Phase2 | Decided
datatype Decision = Undecided | Codeword | Bottom

datatype Node = Node(
    f: nat,
    n: nat,
    id: nat,
    codeword: seq<symbol>,      // my codeword
    symbols: seq<symbol>,       // symbols[j] is the symbol sent by process j
    decision: Decision,         
    state: NodeState,            // current state of the node
    faulty: bool
)


/****************************************************************************************/
/*                                  PROTOCOL STEPS                                      */
/****************************************************************************************/                 

/* Initial state of a participant node */
predicate nodeInit(s: Node, f:nat, n: nat, id: nat)
{
    && n == 3*f + 1
    && 0 <= id < n
    && s.f == f
    && s.n == n
    && s.id == id
    && |s.codeword| == n
    && s.decision == Undecided
    && s.state == Phase1
    && s.faulty == (id < f)
}

/* Transition of a participant node from Phase1 to Phase 2 */
predicate nodeReceiveSymbols(s: Node, s':Node, received_symbols: seq<nat>) 
    requires s.state == Phase1;
    requires |received_symbols| == s.n;
{
    s' == s.(
        symbols := received_symbols,
        state := Phase2)
}

/* Transition of a participant node from Phase2 to Decided */
predicate nodeReceiveSyndromesAndDecide(s: Node, s': Node, syndromes: seq<syndrome>)
    requires s.state == Phase2;
    requires |syndromes| == s.n;
    requires forall syn :: syn in syndromes ==> |syn| == s.n;
{   
    0 <= s.id < s.n
    && if decideOnCodeWord(s, syndromes) then (
        s' == s.(state := Decided,
            decision := Codeword
        )       
    ) else (
        s' == s.(state := Decided,  
            decision := Bottom)
    )
}


/****************************************************************************************/
/*                             FUNCTIONS & PREDICATES                                   */
/****************************************************************************************/ 


/* Evaluates to true iff Node s should decide on its own codeword based on the 
* BCE protocol */
predicate decideOnCodeWord(s: Node, syndromes: seq<syndrome>) 
    requires s.state == Phase2;
    requires s.n > 0;
    requires 0 <= s.id < |syndromes| ;
    requires forall syn :: syn in syndromes ==> |syn| == s.n;
{
    if countTrue(syndromes[s.id]) < s.n - s.f then (
        false
    ) else (
        exists goodSet : multiset<syndrome> :: goodSet <= multiset(syndromes) && goodSyndromeSet(goodSet, s.n, s.n-s.f)
    ) 
}


predicate goodSyndromeSet(syndromes: multiset<syndrome>, n: int, thresh: int) 
    requires n > 0;
    requires forall syn :: syn in syndromes ==> |syn| == n;
{
    |syndromes| >= thresh
    && countMatchingBits(syndromes, n) >= thresh
}

/* Returns the number of indices where all bits at that index are true */
function countMatchingBits(syndromes: multiset<syndrome>, n: int) : int
    requires n > 0;
    requires forall syn :: syn in syndromes ==> |syn| == n;
{
    countMatchingBitsHelper(syndromes, n, n-1)
}

/* Returns the number of indices where all bits at that index are true up to index i-1 */
function countMatchingBitsHelper(syndromes: multiset<syndrome>, n: int, i: int) : int
    decreases i;
    requires 0 <= i < n;
    requires forall syn :: syn in syndromes ==> |syn| == n;
{
    if i == 0 then 0 else
    if allMatchAt(syndromes, n, i) then 1 + countMatchingBitsHelper(syndromes, n, i-1) 
    else countMatchingBitsHelper(syndromes, n, i-1) 
}

/* Returns true if all bits at index i are true */
predicate allMatchAt(syndromes: multiset<syndrome>, n: int, i: int)
    decreases syndromes;
    requires forall syn :: syn in syndromes ==> |syn| == n;
    requires 0 <= i < n;   
{
    if |syndromes| == 0 then true else
    var nextToCheck : syndrome :| nextToCheck in syndromes;
    nextToCheck[i] && allMatchAt(syndromes-multiset{nextToCheck}, n, i) 
}


/* Maps Node s to its syndome */
function computeSyndrome(s: Node) : syndrome
    requires s.n == |s.symbols| == |s.codeword|;
{
    computeSyndromeHelper(s.codeword, s.symbols)   
}

function computeSyndromeHelper(codeword: seq<nat>, symbols: seq<nat>) : syndrome
    decreases codeword, symbols;
    requires |codeword| == |symbols|
{
    if |codeword| == 0 then []
    else computeSyndromeHelper(codeword[..|codeword|-1], symbols[..|symbols|-1]) + [codeword[|codeword|-1] == symbols[|symbols|-1]]
}

/* Maps syndromes_seq to the number of syndromes in syndromes_seq that 
* has #true bits >= thresh */
// function countGoodSyndromes(syndromes_seq: seq<syndrome>, thresh: int) : int
//     decreases syndromes_seq
// {
//     if |syndromes_seq| == 0 then 0 else
//     var x := countTrue(syndromes_seq[|syndromes_seq|-1]);
//     if x >= thresh then 1 + countGoodSyndromes(syndromes_seq[..|syndromes_seq|-1], thresh) else 
//     countGoodSyndromes(syndromes_seq[..|syndromes_seq|-1], thresh)
// }

/* Maps syn to the number of True bits in syn */
function countTrue(syn: syndrome) : int 
    decreases syn
{
    if |syn| == 0 then 0 else (
        if syn[|syn|-1] then 1 + countTrue(syn[..|syn|-1]) else countTrue(syn[..|syn|-1])
    )
}

function countSame(codeword: seq<nat>, symbols: seq<nat>) : int
    decreases codeword, symbols
    requires |codeword| == |symbols|;
{   
    if |codeword| == 0 then 0
    else if codeword[|codeword|-1] == symbols[|symbols|-1] then 
        1 + countSame(codeword[..|codeword|-1], symbols[..|symbols|-1])
    else
        countSame(codeword[..|codeword|-1], symbols[..|symbols|-1])        
}


/****************************************************************************************/
/*                                       LEMMAS                                         */
/****************************************************************************************/ 


lemma lemma_CountSame_Increment_Property(codeword: seq<nat>, symbols: seq<nat>, i: int) 
    decreases codeword, symbols
    requires |codeword| == |symbols|
    requires 0 < i <= |codeword|;
    ensures codeword[i-1] == symbols[i-1] ==> 
        countSame(codeword[..i], symbols[..i]) == 1 + countSame(codeword[..i-1], symbols[..i-1]);
    ensures codeword[i-1] != symbols[i-1] ==> 
        countSame(codeword[..i], symbols[..i]) == countSame(codeword[..i-1], symbols[..i-1]);
{
    var codeword_prefix := codeword[..i];
    var symbols_prefix := symbols[..i];
    if codeword[i-1] == symbols[i-1] {
        assert countSame(codeword_prefix, symbols_prefix) == 1 + countSame(codeword_prefix[..|codeword_prefix|-1], symbols_prefix[..|symbols_prefix|-1]);
    } else {
        assert countSame(codeword_prefix, symbols_prefix) == countSame(codeword_prefix[..|codeword_prefix|-1], symbols_prefix[..|symbols_prefix|-1]);
    }
        assert symbols_prefix[..|symbols_prefix|-1] == symbols[..i-1];
        assert codeword_prefix[..|codeword_prefix|-1] == codeword[..i-1];
}


lemma lemma_Computed_Syndromes_Have_Length_n(s: Node, syn: syndrome)
    requires s.n == |s.symbols| == |s.codeword|;
    requires syn == computeSyndrome(s);
    ensures |syn| == s.n;
{
    lemma_Computed_Syndromes_Have_Length_n_Helper(s.codeword, s.symbols, syn);
}


/* Prove that the result of computeSyndrome(s) is the result of comparing the
* codeword with the symbols received */
lemma lemma_Computed_Syndromes_Is_Correct(s: Node, syn: syndrome)
    requires s.n == |s.symbols| == |s.codeword| == |syn|;
    requires syn == computeSyndrome(s);
    ensures forall i :: 0<= i < s.n ==> syn[i] == (s.symbols[i] == s.codeword[i]);
{
    lemma_Computed_Syndromes_Is_Correct_Helper(s, syn, s.n);
}

lemma {:induction i} lemma_Computed_Syndromes_Is_Correct_Helper(s: Node, syn: syndrome, i: int)
    decreases i;
    requires s.n == |s.symbols| == |s.codeword| == |syn|;
    requires syn == computeSyndromeHelper(s.codeword, s.symbols);
    requires 0 <= i <= s.n;
    ensures forall k :: 0 <= k < i ==> syn[k] == (s.symbols[k] == s.codeword[k]);
{
    if i == 0 {
        assert computeSyndromeHelper(s.codeword[0..i], s.symbols[0..i]) == [];
    } else {
        lemma_Computed_Syndromes_Is_Correct_Helper(s, syn, i-1);
        var codeword_prefix := s.codeword[0..i];
        var symbols_prefix := s.symbols[0..i];
        lemma_Computed_Syndromes_Construction(s, syn, i);
    }
}


/* Prove that 
* computeSyndromeHelper(s.codeword, s.symbols)[..i] == 
* computeSyndromeHelper(s.codeword[..i], s.symbols[..i]) */
lemma {:induction i} lemma_Computed_Syndromes_Construction(s: Node, syn: syndrome, i: int) 
    decreases s.n - i;
    requires s.n == |s.symbols| == |s.codeword| == |syn|;
    requires syn == computeSyndromeHelper(s.codeword, s.symbols);
    requires 0 <= i <= s.n;
    ensures syn[..i] == computeSyndromeHelper(s.codeword[..i], s.symbols[..i]);
{
    if i == s.n {
        assert syn[..i] == syn;
        assert s.codeword[..i] == s.codeword;
        assert s.symbols[..i] ==  s.symbols;
        assert syn[..i] == computeSyndromeHelper(s.codeword[..i], s.symbols[..i]);
    } else {
        lemma_Computed_Syndromes_Construction(s, syn, i + 1);
        var codeword_prefix := s.codeword[..i+1];
        var symbols_prefix := s.symbols[..i+1];
        var ith_syn := codeword_prefix[|codeword_prefix|-1] == symbols_prefix[|symbols_prefix|-1];
        assert computeSyndromeHelper(codeword_prefix, symbols_prefix) ==
            computeSyndromeHelper(codeword_prefix[..|codeword_prefix|-1], symbols_prefix[..|symbols_prefix|-1])
            + [ith_syn];
        assert syn[..i] ==  computeSyndromeHelper(codeword_prefix[..|codeword_prefix|-1], symbols_prefix[..|symbols_prefix|-1]);
        assert codeword_prefix[..|codeword_prefix|-1] == s.codeword[..i];
        assert symbols_prefix[..|symbols_prefix|-1] == s.symbols[..i];
    }
}


/* Prove that computeSyndromeHelper(codeword, symbols) returns a syndrome that has the 
* same length as |codeword| == |symbols| */
lemma {:induction codeword, symbols} lemma_Computed_Syndromes_Have_Length_n_Helper(
    codeword: seq<nat>, symbols: seq<nat>, syn: syndrome) 
    decreases codeword, symbols, syn;
    requires |codeword| == |symbols|;
    requires syn == computeSyndromeHelper(codeword, symbols);
    ensures |syn| == |codeword|;
{
    if |codeword| == 0 {
        assert |syn| == 0;
    } else {
        lemma_Computed_Syndromes_Have_Length_n_Helper(codeword[..|codeword|-1], symbols[..|symbols|-1], syn[..|syn|-1]);
    }
}


lemma lemma_CountTrue_Equals_CountSame(node: Node) 
    requires node.n == |node.symbols| == |node.codeword|;
    ensures countTrue(computeSyndrome(node)) == countSame(node.codeword, node.symbols);
{
    var syn := computeSyndrome(node);
    lemma_Computed_Syndromes_Have_Length_n(node, syn);
    lemma_Computed_Syndromes_Is_Correct(node, syn);
    lemma_CountTrue_Equals_CountSame_Helper(syn, node.codeword, node.symbols, node.n);
    assert syn[..node.n] == syn;
    assert node.codeword[..node.n] == node.codeword;
    assert node.symbols[..node.n] == node.symbols;
}

lemma {:induction i} lemma_CountTrue_Equals_CountSame_Helper(syn: syndrome, codeword: seq<nat>, symbols: seq<nat>, i: int)
    decreases i;
    requires |syn| == |codeword| == |symbols|;
    requires 0 <= i <= |syn|;
    requires forall k :: 0<= k < |syn| ==> syn[k] == (symbols[k] == codeword[k]);
    ensures countTrue(syn[..i]) == countSame(codeword[..i], symbols[..i]);
{
    if i == 0 {
        assert countTrue(syn[..i]) == countSame(codeword[..i], symbols[..i]) == 0;
    } else {
        lemma_CountTrue_Equals_CountSame_Helper(syn, codeword, symbols, i-1);
        lemma_CountSame_Increment_Property(codeword, symbols, i);
        assert syn[i-1] == (symbols[i-1] == codeword[i-1]);
        var syn_prefix := syn[..i];
        if symbols[i-1] == codeword[i-1] {
            assert countTrue(syn_prefix) == countTrue(syn_prefix[..|syn_prefix|-1]) + 1; 
        } else {
            assert countTrue(syn_prefix) == countTrue(syn_prefix[..|syn_prefix|-1]); 
        }
        assert syn_prefix[..|syn_prefix|-1] == syn[..i-1];
    }
} 


}
