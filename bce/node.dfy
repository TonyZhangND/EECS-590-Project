module BCE_Protocol_Node {

type symbol = nat
type syndrome = seq<bool>

datatype NodeState = Phase1 | Phase2 | Decided
datatype Decision = Codeword | Bottom

datatype Node = Node(
    f: nat,
    n: nat,
    id: nat,
    codeword: seq<symbol>,      // my codeword
    symbols: seq<symbol>,       // symbols[j] is the symbol sent by process j
    decision: Decision,         
    state: NodeState            // current state of the node
)


/****************************************************************************************/
/*                                  PROTOCOL STEPS                                      */
/****************************************************************************************/                 

/* Initial state of a participant node */
predicate nodeInit(s: Node, f:nat, n: nat, id: nat)
    requires n == 3*f + 1;
    requires 0 <= id < n;
{
    && s.f == f
    && s.n == n
    && s.id == id
    && |s.codeword| == n
    && s.state == Phase1
}

/* Transition of a participant node from Phase1 to Phase 2 */
predicate nodeReceiveSymbols(s: Node, s':Node, received_symbols: seq<nat>) 
    requires s.n == 3*s.f + 1;
    requires 0 <= s.id < s.n;
    requires nodeInit(s, s.f, s.n, s.id);
    requires |received_symbols| == |s.codeword|;  // received_symbols is of correct length
    requires received_symbols[s.id] == s.codeword[s.id]; // don't deceive myself
{
    s' == s.(
        symbols := received_symbols,
        state := Phase2)
}

/* Transition of a participant node from Phase2 to Decided */
predicate nodeReceiveSyndromesAndDecide(s: Node, s': Node, syndromes: seq<syndrome>)
    requires s.n == 3*s.f + 1;
    requires s.state == Phase2;
    requires 0 <= s.id < s.n;
    requires s.n == |s.symbols| == |s.codeword|;
    requires s.codeword[s.id] == s.symbols[s.id];
    requires s.n == |syndromes|
{   
    if decideOnCodeWord(s, syndromes) then (
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
    requires s.n == 3*s.f + 1;
    requires s.state == Phase2;
    requires 0 <= s.id < s.n;
    requires s.n == |s.symbols| == |s.codeword|;
    requires s.codeword[s.id] == s.symbols[s.id];
    requires s.n == |syndromes|
{
    if countTrue(syndromes[s.id]) < s.n - s.f then (
        false
    ) else (
        countGoodSyndromes(syndromes, s.n-s.f) >= s.n - s.f
    ) 

}

/* Maps Node s to its syndome */
function computeSyndrome(s: Node) : syndrome
    requires s.state == Phase2;
    requires 0 <= s.id < s.n;
    requires s.n == |s.symbols| == |s.codeword|;
    requires s.codeword[s.id] == s.symbols[s.id];
{
    computeSyndromeHelper(s.codeword, s.symbols)   
}

function computeSyndromeHelper(codeword: seq<nat>, symbols: seq<nat>) : syndrome
    decreases codeword, symbols;
    requires |codeword| == |symbols|
{
    if |codeword| == 0 then []
    else [codeword[0] == symbols[0]] + computeSyndromeHelper(codeword[1..], symbols[1..])
}

/* Maps syndromes_seq to the number of syndromes in syndromes_seq that 
* has #true bits >= thresh */
function countGoodSyndromes(syndromes_seq: seq<syndrome>, thresh: int) : int
    decreases syndromes_seq
{
    if |syndromes_seq| == 0 then 0 else
    var x := countTrue(syndromes_seq[0]);
    if x >= thresh then 1 + countGoodSyndromes(syndromes_seq[1..], thresh) else 
    countGoodSyndromes(syndromes_seq[1..], thresh)
}

/* Maps syn to the number of True bits in syn */
function countTrue(syn: syndrome) : int 
    decreases syn
{
    if |syn| == 0 then 0 else (
        if syn[0] then 1 + countTrue(syn[1..]) else countTrue(syn[1..])
    )
}
}
