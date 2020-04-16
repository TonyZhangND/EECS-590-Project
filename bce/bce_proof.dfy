include "service.dfy"
include "node.dfy"

module BCE_Proof {
import opened BCE_Protocol_Service
import opened BCE_Protocol_Node


/****************************************************************************************/
/*                                   Equivalence                                        */
/****************************************************************************************/ 
lemma lemma_BCE_Equivalence(s:Service, s':Service, s'':Service) 
    requires BCE(s, s', s'');
    ensures forall node :: 
        node in s''.nodes && !node.faulty && node.decision != Bottom 
        ==> 
        node.decision == Codeword;
{}


/****************************************************************************************/
/*                                  Termination                                         */
/****************************************************************************************/ 

lemma lemma_BCE_Termination(s:Service, s':Service, s'':Service) 
    requires BCE(s, s', s'');
    ensures forall node :: 
        node in s''.nodes && !node.faulty 
        ==> 
        (node.decision == Codeword || node.decision == Bottom);
{}


/****************************************************************************************/
/*                                     Validity                                         */
/****************************************************************************************/ 

/*
- At the end of round 1: >= n-f symbols in Symbols are common, v;
- Each non faulty calculates syndrome: InSymbol VS Symbols
    * >= n-f of the same bits must be true in Syndromes for all non faulty
- Send syndromes. At the end of round 2: each non faulty has >= n-f sydromes ==> decide
*/
lemma lemma_BCE_Validity(s:Service, s':Service, s'':Service) 
    requires BCE(s, s', s'');
    requires forall node1, node2 :: 
            && node1 in s.nodes && node2 in s.nodes 
            && !node1.faulty && !node2.faulty ==> 
            node1.codeword == node2.codeword;
    ensures 
        forall node :: 
            node in s''.nodes && !node.faulty 
            ==> 
            node.decision == Codeword;
{
    lemma_Service_Maintains_Invariants(s, s', s'');
    assert forall node :: node in s'.nodes && !node.faulty ==> node.state == Phase2;
    lemma_BCE_Validity_Receive_n_f_Common_Symbols(s, s');
    var syndromes := syndromesToExchange(s'.nodes);
    lemma_Exchanged_Syndromes_Are_Extracted(s'.nodes);
    lemma_BCE_Validity_Correct_Nodes_Decide_Codeword(s', syndromes);
}

// TODO: Yuwei
lemma lemma_BCE_Validity_Receive_n_f_Common_Symbols(s:Service, s':Service) 
    requires serviceInit(s);
    requires serviceExchangeSymbols(s, s');
    requires node_invariants(s');
    requires |s.nodes| == s.n;
    requires |s'.nodes| == s'.n;
    requires s.n == s'.n;
    requires forall node :: node in s.nodes ==> 0 <= node.id < s.n;
    requires forall node :: node in s.nodes ==> |node.codeword| == s.n;
    //requires forall node :: node in s.nodes ==> |node.symbols| == s.n;
    requires forall node :: node in s'.nodes ==> |node.codeword| == s'.n;
    //requires forall node :: node in s'.nodes ==> |node.symbols| == s'.n;
    requires forall  i :: 0 <= i < s.n ==> s.nodes[i].id == i;
    requires forall  i :: 0 <= i < s'.n ==> s'.nodes[i].id == i;
    //requires forall node :: node in s.nodes ==> node.n == |node.symbols| == |node.codeword|;
    //requires forall node :: node in s'.nodes ==> node.n == |node.symbols| == |node.codeword|;
    requires forall node1, node2 :: 
            && node1 in s.nodes && node2 in s.nodes 
            && !node1.faulty && !node2.faulty ==> 
            node1.codeword == node2.codeword;
    ensures forall node :: 
        && node in s'.nodes && !node.faulty
        ==>
        node.symbols == node.codeword;
{
    var symbols := symbolsToExchange(s.nodes);
    lemma_Extract_Generates_One_Symbol_For_Each_Node(s.nodes);
    lemma_Exchanged_Symbols_Are_Extracted(s.nodes);
    assert forall j :: 0 <= j < |symbols| ==> |symbols[j]| == |s.nodes|;
    assert (forall j :: 0 <= j < |symbols| ==>
        (forall  i :: 0 <= i < s'.n ==> 
            nodeReceiveSymbols(s.nodes[i], s'.nodes[i], symbols[j])));
}


// TONY
lemma lemma_BCE_Validity_Correct_Nodes_Decide_Codeword(s':Service, syndromes: seq<seq<syndrome>>) 
    requires node_invariants(s');
    requires |s'.nodes| == s'.n;
    requires forall  i :: 0 <= i < s'.n ==> s'.nodes[i].id == i
    requires forall node :: node in s'.nodes ==> node.n == |node.symbols| == |node.codeword|;
    requires syndromes == syndromesToExchange(s'.nodes);
    requires |syndromes| == s'.n;
    requires forall node :: 
        node in s'.nodes && !node.faulty
        ==>
        && node.symbols == node.codeword
        && node.state == Phase2
        && 0 <= node.id < s'.n
        && 0 <= node.id < |syndromes[node.id]|;
    ensures forall node :: 
        node in s'.nodes && !node.faulty ==> decideOnCodeWord(node, syndromes[node.id]);
{
    lemma_Exchanged_Syndromes_Are_Extracted(s'.nodes);
    forall node | node in s'.nodes && !node.faulty
    ensures decideOnCodeWord(node, syndromes[node.id])
    {
        var syndromes_received := syndromes[node.id];
        assert syndromes_received == extractSyndromes(s'.nodes);
        lemma_Extracted_Syndromes_Are_Computed(s'.nodes);
        var my_syndrome := syndromes_received[node.id];
        assert node == s'.nodes[node.id];
        assert my_syndrome == computeSyndrome(node);
        lemma_Computed_Syndromes_Have_Length_n(node, my_syndrome);
        lemma_BCE_Validity_Correct_Nodes_Own_Syndrome_Is_Good(node, my_syndrome);
        assert countTrue(syndromes_received[node.id]) >= node.n - node.f;
        assert countGoodSyndromes(syndromes_received, node.n-node.f) >= node.n - node.f;
    }
}


lemma {:induction my_syndrome} lemma_BCE_Validity_Correct_Nodes_Own_Syndrome_Is_Good(node: Node, my_syndrome: syndrome) 
    requires !node.faulty;
    requires node.state == Phase2;
    requires |my_syndrome| == node.n;
    requires node.n == 3 * node.f + 1
    ensures countTrue(my_syndrome) >= node.n - node.f;
{

}


/****************************************************************************************/
/*                                Service Invariants                                    */
/****************************************************************************************/ 


predicate node_invariants(s: Service)
{
    forall node :: node in s.nodes && !node.faulty ==>
    && node.n == node.f * 3 + 1
    && 0 <= node.id < node.n
    && 0 <= node.id < node.n
    && |node.codeword| == node.n
    && node.n == s.n
    && node.f == s.f
}

predicate service_invariants(s:Service, s':Service, s'':Service)
{
    BCE(s, s', s'')
    ==>
    && serviceInit(s)
    && node_invariants(s) && node_invariants(s') && node_invariants(s'')
    && node_membership_invariant(s, s', s'')
    // correctness of each node is constant
    && node_faultiness_invariant(s, s', s'')
    // id of each node is constant
    && node_identity_invariant(s, s', s'')
}

// num of nodes is constant
predicate node_membership_invariant(s:Service, s':Service, s'':Service)
{
    && |s.nodes| == |s'.nodes| == |s''.nodes| == s.n
    && s.n == s'.n == s''.n
}

// correctness of each node is constant
predicate node_faultiness_invariant(s:Service, s':Service, s'':Service) 
    requires node_membership_invariant(s, s', s'');
{
    && s.f == s'.f == s''.f
    && (forall  id :: 0 <= id < s.n ==> s.nodes[id].faulty == s'.nodes[id].faulty == s''.nodes[id].faulty)
}

// identity of each node is constant
predicate node_identity_invariant(s:Service, s':Service, s'':Service)
    requires node_membership_invariant(s, s', s'');
{
    forall  i :: 0 <= i < s.n 
    ==> 
    && s.nodes[i].id == i
    && s'.nodes[i].id == i
    && s''.nodes[i].id == i
}

lemma lemma_Service_Maintains_Invariants(s:Service, s':Service, s'':Service) 
    requires BCE(s, s', s'');
    ensures service_invariants(s, s', s'');
{}
}