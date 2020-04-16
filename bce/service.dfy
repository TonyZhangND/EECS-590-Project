include "node.dfy"

module BCE_Protocol_Service {
import opened BCE_Protocol_Node

datatype ServiceState = SPhase1 | SPhase2 | SDecided

datatype Service = Service(
    nodes: seq<Node>,
    n: nat,
    f: nat,
    state: ServiceState
)


/****************************************************************************************/
/*                                  PROTOCOL STEPS                                      */
/****************************************************************************************/   


/* True iff Service state s is a valid initial state

To prove BCE, I don't have to start from a value and then encode/decode the value. 
I can start immediately with a codeword. There are conditions to starting directly with a 
codeword that bounds the initial state. 
For any two correct processes, if their initial codewords differ, then they must 
have at most k-1 (n-2f-1) symbols in common. Else they would have began with the same 
value and started with the same codeword. */
predicate serviceInit(s: Service)
{
    && s.f > 0
    && s.n == 3*s.f + 1
    && |s.nodes| == s.n
    && forall id :: 0 <= id < |s.nodes| ==> nodeInit(s.nodes[id], s.f, s.n, id)
    && s.state == SPhase1
}

predicate serviceExchangeSymbols(s: Service, s': Service) 
    requires serviceInit(s);
{
    var symbolsForExchange := symbolsToExchange(s.nodes);
    // symbolsForExchange[i] is the seq of symbols that node i receives.
    // For any node i, symbolsForExchange[i][j] contains the jth symbol of node j.
    lemma_Exchanged_Symbols_Are_Extracted(s.nodes);
    && s' == s.(nodes := s'.nodes, state := SPhase2)
    && |s'.nodes| == |s.nodes|
    && forall id :: 0 <= id < |s.nodes| ==> 
        // assert symbolsForExchange[id][id] == s.nodes[id].codeword[id];  // TODO
        nodeReceiveSymbols(s.nodes[id], s'.nodes[id], symbolsForExchange[id])
}

predicate serviceExchangeSyndromesAndDecide(s: Service, s': Service) 
    requires s.state == SPhase2
    requires forall sn :: sn in s.nodes ==> sn.n == |sn.symbols| == |sn.codeword|;
    requires forall sn :: sn in s.nodes ==> sn.state == Phase2;
{
    var syndromesForExchange := syndromesToExchange(s.nodes);
    lemma_Exchanged_Syndromes_Are_Extracted(s.nodes);

    && s' == s.(nodes := s'.nodes, state := SDecided)
    && |s'.nodes| == |s.nodes|
    && forall id :: 0 <= id < |s.nodes| ==> 
        |syndromesForExchange[id]| == s.nodes[id].n
        && nodeReceiveSyndromesAndDecide(s.nodes[id], s'.nodes[id], syndromesForExchange[id])
}


predicate BCE(s:Service, s':Service, s'':Service)
{
    if serviceInit(s) then
        lemma_Exchanged_Symbols_Are_Extracted(s.nodes);
        && serviceInit(s)
        && serviceExchangeSymbols(s, s')
        && serviceExchangeSyndromesAndDecide(s', s'')
    else 
        false
}


/****************************************************************************************/
/*                             FUNCTIONS & PREDICATES                                   */
/****************************************************************************************/ 


/* Helper function for SPhase1 -> SPhase2 transition. 
* symbolsToExchange(nodes)[i] represents the seq of symbols that nodes[i] receives in 
* the exhange phase */
function symbolsToExchange(nodes: seq<Node>) : seq<seq<symbol>> 
    requires forall s :: s in nodes ==> 0 <= s.id < s.n;
    requires forall s :: s in nodes ==> |s.codeword| == s.n;
{
    symbolsToExchangeHelper(nodes, 0)
}


function symbolsToExchangeHelper(nodes: seq<Node>, i: nat) : seq<seq<symbol>> 
    decreases |nodes| - i;
    requires 0 <= i <= |nodes|;
    requires forall s :: s in nodes ==> 0 <= s.id < s.n;
    requires forall s :: s in nodes ==> |s.codeword| == s.n;
{
    if i == |nodes| then [] else
    [extractSymbols(nodes)] + symbolsToExchangeHelper(nodes, i + 1)
}

/* Helper function that generates a single seq<symbol> for exchange. 
* This is where Byzantine behavior can be modeled */
function extractSymbols(nodes: seq<Node>) : seq<symbol> 
    decreases nodes;
    // requires forall s :: s in nodes ==> s.n == 3*s.f + 1;
    requires forall s :: s in nodes ==> 0 <= s.id < s.n;
    requires forall s :: s in nodes ==> |s.codeword| == s.n;
{
    if |nodes| == 0 then [] else
    [nodes[0].codeword[nodes[0].id]] + extractSymbols(nodes[1..])
}



/* Helper function for SPhase2 -> SDecided transition. 
* syndromeToExchange(nodes)[i] represents the seq of syndromes that nodes[i] receives in 
* the exhange phase */
function syndromesToExchange(nodes: seq<Node>) : seq<seq<syndrome>> 
    requires forall s :: s in nodes ==> s.n == |s.symbols| == |s.codeword|;
{
    syndromesToExchangeHelper(nodes, 0)
}


function syndromesToExchangeHelper(nodes: seq<Node>, i: nat) : seq<seq<syndrome>> 
    decreases |nodes| - i;
    requires 0 <= i <= |nodes|;
    requires forall s :: s in nodes ==> s.n == |s.symbols| == |s.codeword|;
{
    if i == |nodes| then [] else
    [extractSyndromes(nodes)] + syndromesToExchangeHelper(nodes, i + 1)
}

/* Helper function that generates a single seq<syndrome> for exchange. 
* This is where Byzantine behavior can be modeled */
function extractSyndromes(nodes: seq<Node>) : seq<syndrome> 
    decreases nodes;
    requires forall s :: s in nodes ==> s.n == |s.symbols| == |s.codeword|;
{
    if |nodes| == 0 then [] else
    [computeSyndrome(nodes[0])] + extractSyndromes(nodes[1..])
}

/****************************************************************************************/
/*                                       LEMMAS                                         */
/****************************************************************************************/ 


/* Proof that for any nodes: seq<Node>, |symbolsToExchange(nodes)| == |nodes| */
lemma {:induction i} lemma_Exchange_Generates_One_SymbolSeq_For_Each_Node(nodes: seq<Node>, i:nat) 
    decreases |nodes| - i;
    requires 0 <= i <= |nodes|;
    requires forall s :: s in nodes ==> 0 <= s.id < s.n;
    requires forall s :: s in nodes ==> |s.codeword| == s.n;
    requires symbolsToExchangeHelper(nodes, 0) == symbolsToExchange(nodes);
    ensures |symbolsToExchangeHelper(nodes, i)| == |nodes[i..]|;
{
    if i == |nodes| {
        assert |symbolsToExchangeHelper(nodes, i)| == 0;
    } else {
        lemma_Exchange_Generates_One_SymbolSeq_For_Each_Node(nodes, i+1);
    }
}


/* Proof that for any nodes: seq<Node>, |extractSymbols(nodes)| == |nodes| */
lemma {:induction nodes} lemma_Extract_Generates_One_Symbol_For_Each_Node(nodes: seq<Node>) 
    requires forall s :: s in nodes ==> 0 <= s.id < s.n;
    requires forall s :: s in nodes ==> |s.codeword| == s.n;
    ensures |extractSymbols(nodes)| == |nodes|;
{}


/* Wrapper for lemma_Exchanged_Symbols_Are_Extracted_Helper */
lemma {:induction nodes} lemma_Exchanged_Symbols_Are_Extracted(nodes: seq<Node>) 
    requires forall s :: s in nodes ==> 0 <= s.id < s.n;
    requires forall s :: s in nodes ==> |s.codeword| == s.n;
    ensures |symbolsToExchange(nodes)| == |nodes|;
    ensures |extractSymbols(nodes)| == |nodes|;
    ensures forall id :: 0 <= id < |symbolsToExchange(nodes)| ==> |symbolsToExchange(nodes)[id]| == |nodes|;
{
    lemma_Exchanged_Symbols_Are_Extracted_Helper(nodes, 0);
}

/* Proof that every element of symbolsToExchange(nodes) is an instance of extractSymbols(nodes) */
lemma  {:induction i} lemma_Exchanged_Symbols_Are_Extracted_Helper(nodes: seq<Node>, i: nat) 
    decreases |nodes| - i;
    requires 0 <= i <= |nodes|;
    requires forall s :: s in nodes ==> 0 <= s.id < s.n;
    requires forall s :: s in nodes ==> |s.codeword| == s.n;
    ensures |symbolsToExchange(nodes)| == |nodes|;
    ensures |extractSymbols(nodes)| == |nodes|;
    ensures forall id :: 0 <= id < |symbolsToExchangeHelper(nodes, i)| ==> |symbolsToExchangeHelper(nodes, i)[id]| == |nodes|;
{
    lemma_Extract_Generates_One_Symbol_For_Each_Node(nodes);
    lemma_Exchange_Generates_One_SymbolSeq_For_Each_Node(nodes, 0);
    if i == |nodes| {
        assert symbolsToExchangeHelper(nodes, i) == [];
        assert forall id :: i <= id < |symbolsToExchangeHelper(nodes, i)| ==> symbolsToExchangeHelper(nodes, i)[id] == extractSymbols(nodes);
    } else {
        lemma_Exchanged_Symbols_Are_Extracted_Helper(nodes, i+1);
    }
}



/* Proof that for any nodes: seq<Node>, |syndromesToExchange(nodes)| == |nodes| */
lemma {:induction i} lemma_Exchange_Generates_One_SydromeSeq_For_Each_Node(nodes: seq<Node>, i:nat) 
    decreases |nodes| - i;
    requires 0 <= i <= |nodes|;
    requires forall s :: s in nodes ==> s.n == |s.symbols| == |s.codeword|;
    requires syndromesToExchangeHelper(nodes, 0) == syndromesToExchange(nodes);
    ensures |syndromesToExchangeHelper(nodes, i)| == |nodes[i..]|;
{
    if i == |nodes| {
        assert |syndromesToExchangeHelper(nodes, i)| == 0;
    } else {
        lemma_Exchange_Generates_One_SydromeSeq_For_Each_Node(nodes, i+1);
    }
}


/* Proof that for any nodes: seq<Node>, |extractSyndromes(nodes)| == |nodes| */
lemma {:induction nodes} lemma_Extract_Generates_One_Syndrome_For_Each_Node(nodes: seq<Node>) 
    decreases nodes;
    requires forall s :: s in nodes ==> s.n == |s.symbols| == |s.codeword|;
    ensures |extractSyndromes(nodes)| == |nodes|;
    ensures forall i :: 0 <= i < |nodes| ==> |extractSyndromes(nodes)[i]| == nodes[i].n;
    ensures forall i :: 0 <= i < |nodes| ==> extractSyndromes(nodes)[i] == computeSyndrome(nodes[i]);
{
    if |nodes| == 0 {
        assert |extractSyndromes(nodes)| == 0;
    } else {
        var node0 := nodes[0];
        var syn0 := computeSyndrome(node0);
        assert extractSyndromes(nodes)[0] == syn0;
        lemma_Computed_Syndromes_Have_Length_n(node0, syn0);
        lemma_Extract_Generates_One_Syndrome_For_Each_Node(nodes[1..]);
    }
}


/* Wrapper for lemma_Exchanged_Syndromes_Are_Extracted_Helper */
lemma {:induction nodes} lemma_Exchanged_Syndromes_Are_Extracted(nodes: seq<Node>) 
    requires forall s :: s in nodes ==> s.n == |s.symbols| == |s.codeword|;
    ensures |syndromesToExchange(nodes)| == |nodes|;
    ensures |extractSyndromes(nodes)| == |nodes|;
    ensures forall id :: 0 <= id < |syndromesToExchange(nodes)| ==> syndromesToExchange(nodes)[id] == extractSyndromes(nodes);
{
    lemma_Exchanged_Syndromes_Are_Extracted_Helper(nodes, 0);
}

/* Proof that every element of syndromesToExchange(nodes) is an instance of extractSyndromes(nodes) */
lemma  {:induction i} lemma_Exchanged_Syndromes_Are_Extracted_Helper(nodes: seq<Node>, i: nat) 
    decreases |nodes| - i;
    requires 0 <= i <= |nodes|;
    requires forall s :: s in nodes ==> s.n == |s.symbols| == |s.codeword|;
    ensures |syndromesToExchange(nodes)| == |nodes|;
    ensures |extractSyndromes(nodes)| == |nodes|;
    ensures forall id :: 0 <= id < |syndromesToExchangeHelper(nodes, i)| ==> syndromesToExchangeHelper(nodes, i)[id] == extractSyndromes(nodes);
{
    lemma_Extract_Generates_One_Syndrome_For_Each_Node(nodes);
    lemma_Exchange_Generates_One_SydromeSeq_For_Each_Node(nodes, 0);
    if i == |nodes| {
        assert syndromesToExchangeHelper(nodes, i) == [];
        assert forall id :: i <= id < |syndromesToExchangeHelper(nodes, i)| ==> syndromesToExchangeHelper(nodes, i)[id] == extractSyndromes(nodes);
    } else {
        lemma_Exchanged_Syndromes_Are_Extracted_Helper(nodes, i+1);
    }
}


/* Proof that extractSyndromes(nodes)[i] == computeSyndrome(nodes[i])  */
lemma {:induction nodes} lemma_Extracted_Syndromes_Are_Computed(nodes: seq<Node>) 
    requires forall s :: s in nodes ==> s.n == |s.symbols| == |s.codeword|;
    ensures |extractSyndromes(nodes)| == |nodes|
    ensures forall id :: 0 <= id < |extractSyndromes(nodes)| ==> extractSyndromes(nodes)[id] == computeSyndrome(nodes[id]);
{}
}