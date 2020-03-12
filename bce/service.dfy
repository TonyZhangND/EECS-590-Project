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
    lemma_Exchange_Generates_One_SymbolSeq_For_Each_Node(s.nodes);
    lemma_Extract_Generates_One_Symbol_For_Each_Node(s.nodes);
    lemma_Exchanged_Symbols_Are_Extracted(s.nodes, symbolsForExchange, 0);
    assert |symbolsForExchange| == |s.nodes|;
    && s' == s.(nodes := s'.nodes)
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
    decreases nodes;
    requires forall s :: s in nodes ==> s.n == 3*s.f + 1;
    requires forall s :: s in nodes ==> 0 <= s.id < s.n;
    requires forall s :: s in nodes ==> nodeInit(s, s.f, s.n, s.id)
{
    if |nodes| == 0 then [] else
    [extractSymbols(nodes)] + symbolsToExchange(nodes[1..])
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
lemma {:induction nodes} lemma_Exchange_Generates_One_SymbolSeq_For_Each_Node(nodes: seq<Node>) 
    requires forall s :: s in nodes ==> s.n == 3*s.f + 1;
    requires forall s :: s in nodes ==> 0 <= s.id < s.n;
    requires forall s :: s in nodes ==> nodeInit(s, s.f, s.n, s.id)
    ensures |symbolsToExchange(nodes)| == |nodes|;
{}


/* Proof that for any nodes: seq<Node>, |extractSymbols(nodes)| == |nodes| */
lemma {:induction nodes} lemma_Extract_Generates_One_Symbol_For_Each_Node(nodes: seq<Node>) 
    requires forall s :: s in nodes ==> s.n == 3*s.f + 1;
    requires forall s :: s in nodes ==> 0 <= s.id < s.n;
    requires forall s :: s in nodes ==> nodeInit(s, s.f, s.n, s.id)
    ensures |extractSymbols(nodes)| == |nodes|;
{}


lemma  {:induction nodes} lemma_Exchanged_Symbols_Are_Extracted(nodes: seq<Node>, symbolsForExchange: seq<seq<symbol>>, i: nat) 
    requires forall s :: s in nodes ==> s.n == 3*s.f + 1;
    requires forall s :: s in nodes ==> 0 <= s.id < s.n;
    requires forall s :: s in nodes ==> nodeInit(s, s.f, s.n, s.id)
    ensures forall id :: 0 <= id < |symbolsForExchange| ==> symbolsForExchange[id] == extractSymbols(nodes);
{
    //TODO
}


}