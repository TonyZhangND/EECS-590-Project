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


/* True iff Service state s is a valid initial state */
predicate serviceInit(s: Service)
{
    && s.f > 0
    && s.n == 3*s.f + 1
    && |s.nodes| == s.n
    && forall id :: 0 <= id < |s.nodes| ==> nodeInit(s.nodes[id], s.f, s.n, id)
    && s.state == SPhase1
}

predicate serviceExchangeSymbols(s: Service, s': Service) 
    requires serviceInit(s)
{
    var symbolsForExchange := symbolsToExchange(s.nodes);
    // symbolsForExchange[i] is the seq of symbols that node i receives.
    // For any node i, symbolsForExchange[i][j] contains the jth symbol of node j.
    lemma_Exchanged_Symbols_Are_Extracted(s.nodes);
    && s' == s.(nodes := s'.nodes, state := SPhase2)
    && |s'.nodes| == |s.nodes|
    && forall id :: 0 <= id < |s.nodes| ==> 
        assert symbolsForExchange[id][id] == s.nodes[id].codeword[id];
        nodeReceiveSymbols(s.nodes[id], s'.nodes[id], symbolsForExchange[id])
}


predicate serviceNext(s:Service, s':Service)
{
    // TODO
    true
}


/****************************************************************************************/
/*                             FUNCTIONS & PREDICATES                                   */
/****************************************************************************************/ 


/* Helper function for SPhase1 -> SPhase2 transition. 
* symbolsToExchange(nodes)[i] represents the seq of symbols that nodes[i] receives in 
* the exhange phase */
function symbolsToExchange(nodes: seq<Node>) : seq<seq<symbol>> 
    requires forall s :: s in nodes ==> s.n == 3*s.f + 1;
    requires forall s :: s in nodes ==> 0 <= s.id < s.n;
    requires forall s :: s in nodes ==> nodeInit(s, s.f, s.n, s.id)
{
    symbolsToExchangeHelper(nodes, 0)
}


function symbolsToExchangeHelper(nodes: seq<Node>, i: nat) : seq<seq<symbol>> 
    decreases |nodes| - i;
    requires 0 <= i <= |nodes|;
    requires forall s :: s in nodes ==> s.n == 3*s.f + 1;
    requires forall s :: s in nodes ==> 0 <= s.id < s.n;
    requires forall s :: s in nodes ==> nodeInit(s, s.f, s.n, s.id)
{
    if i == |nodes| then [] else
    [extractSymbols(nodes)] + symbolsToExchangeHelper(nodes, i + 1)
}

/* Helper function that generates a single seq<symbol> for exchange. 
* This is where Byzantine behavior can be modeled */
function extractSymbols(nodes: seq<Node>) : seq<symbol> 
    decreases nodes;
    requires forall s :: s in nodes ==> s.n == 3*s.f + 1;
    requires forall s :: s in nodes ==> 0 <= s.id < s.n;
    requires forall s :: s in nodes ==> nodeInit(s, s.f, s.n, s.id)
{
    if |nodes| == 0 then [] else
    [nodes[0].codeword[nodes[0].id]] + extractSymbols(nodes[1..])
}


/****************************************************************************************/
/*                                       LEMMAS                                         */
/****************************************************************************************/ 


/* Proof that for any nodes: seq<Node>, |symbolsToExchange(nodes)| == |nodes| */
lemma {:induction i} lemma_Exchange_Generates_One_SymbolSeq_For_Each_Node(nodes: seq<Node>, i:nat) 
    decreases |nodes| - i;
    requires 0 <= i <= |nodes|;
    requires forall s :: s in nodes ==> s.n == 3*s.f + 1;
    requires forall s :: s in nodes ==> 0 <= s.id < s.n;
    requires forall s :: s in nodes ==> nodeInit(s, s.f, s.n, s.id)
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
    requires forall s :: s in nodes ==> s.n == 3*s.f + 1;
    requires forall s :: s in nodes ==> 0 <= s.id < s.n;
    requires forall s :: s in nodes ==> nodeInit(s, s.f, s.n, s.id)
    ensures |extractSymbols(nodes)| == |nodes|;
{}


/* Wrapper for lemma_Exchanged_Symbols_Are_Extracted_Helper */
lemma {:induction nodes} lemma_Exchanged_Symbols_Are_Extracted(nodes: seq<Node>) 
    requires forall s :: s in nodes ==> s.n == 3*s.f + 1;
    requires forall s :: s in nodes ==> 0 <= s.id < s.n;
    requires forall s :: s in nodes ==> nodeInit(s, s.f, s.n, s.id);
    ensures |symbolsToExchange(nodes)| == |nodes|;
    ensures |extractSymbols(nodes)| == |nodes|;
    ensures forall id :: 0 <= id < |symbolsToExchange(nodes)| ==> symbolsToExchange(nodes)[id] == extractSymbols(nodes);
{
    lemma_Exchanged_Symbols_Are_Extracted_Helper(nodes, 0);
}

/* Proof that every element of symbolsToExchange(nodes) is an instance of extractSymbols(nodes) */
lemma  {:induction i} lemma_Exchanged_Symbols_Are_Extracted_Helper(nodes: seq<Node>, i: nat) 
    decreases |nodes| - i;
    requires 0 <= i <= |nodes|;
    requires forall s :: s in nodes ==> s.n == 3*s.f + 1;
    requires forall s :: s in nodes ==> 0 <= s.id < s.n;
    requires forall s :: s in nodes ==> nodeInit(s, s.f, s.n, s.id);
    ensures |symbolsToExchange(nodes)| == |nodes|;
    ensures |extractSymbols(nodes)| == |nodes|;
    ensures forall id :: 0 <= id < |symbolsToExchangeHelper(nodes, i)| ==> symbolsToExchangeHelper(nodes, i)[id] == extractSymbols(nodes);
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
}