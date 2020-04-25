include "../Libraries/common.dfy"
include "service.dfy"
include "node.dfy"
include "service_invariants.dfy"

module BCE_Proof {
import opened BCE_Protocol_Service
import opened BCE_Protocol_Node
import opened Service_Invariants
import opened Libraries_Common


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
    ensures 
        (forall node1, node2 :: 
            && node1 in s.nodes && node2 in s.nodes 
            && !node1.faulty && !node2.faulty ==> 
            node1.codeword == node2.codeword)
        ==>
        (forall node :: 
            node in s''.nodes && !node.faulty 
            ==> 
            node.decision == Codeword);
{
    lemma_Service_Maintains_Invariants(s, s', s'');
    lemma_BCE_Validity_Receive_n_f_Common_Symbols(s, s');
    assert forall node :: node in s'.nodes && !node.faulty ==> node.state == Phase2;
    var syndromes := syndromesToExchange(s'.nodes);
    lemma_Exchanged_Syndromes_Are_Extracted(s'.nodes);
    lemma_BCE_Validity_Correct_Nodes_Decide_Codeword(s', syndromes);
}

// TODO: Yuwei
lemma lemma_BCE_Validity_Receive_n_f_Common_Symbols(s:Service, s':Service) 
    requires serviceInit(s);
    requires serviceExchangeSymbols(s, s');
    ensures forall node :: 
        && node in s'.nodes && !node.faulty
        ==>
        node.symbols == node.codeword;
{}


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
        && node.symbols == node.codeword  //by "everyone is behaving" temporary assumption
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
        var syndromes_received := syndromes[node.id];  // seq of syndromes received by node.id
        assert syndromes_received == extractSyndromes(s'.nodes);
        lemma_Extracted_Syndromes_Are_Computed(s'.nodes);
        var my_syndrome := syndromes_received[node.id]; // syndome computed by node.id for itself
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
    requires node.n == |node.symbols| == |node.codeword|; 
    requires node.symbols == node.codeword; //by "everyone is behaving" temporary assumption
    requires my_syndrome == computeSyndrome(node);
    ensures countTrue(my_syndrome) >= node.n - node.f;
{
    assert |computeSyndrome(node)| == node.n;
    assert my_syndrome[0..node.n] == my_syndrome;
    lemma_BCE_Validity_Correct_Nodes_Own_Syndrome_Is_Good_Helper(node, my_syndrome, node.n);
}


lemma {:induction i} lemma_BCE_Validity_Correct_Nodes_Own_Syndrome_Is_Good_Helper(node: Node, my_syndrome: syndrome, i: int) 
    decreases i;
    requires !node.faulty;
    requires node.state == Phase2;
    requires |my_syndrome| == node.n;
    requires node.n == 3 * node.f + 1
    requires node.n == |node.symbols| == |node.codeword|; 
    requires node.symbols == node.codeword; //by "everyone is behaving" temporary assumption
    requires my_syndrome == computeSyndrome(node);
    requires 0 <= i <= node.n;
    ensures countTrue(my_syndrome[0..i]) >= i - node.f;
{
    if i == 0 {
        assert my_syndrome[0..i] == [];
        assert countTrue(my_syndrome[0..i]) == 0;
    } else {
        lemma_BCE_Validity_Correct_Nodes_Own_Syndrome_Is_Good_Helper(node, my_syndrome, i-1);
        assert countTrue(my_syndrome[0..i-1]) >= i-1 - node.f;
        assert node.symbols[i-1] == node.codeword[i-1];
        lemma_Computed_Syndromes_Is_Correct(node, my_syndrome);
        assert my_syndrome[i-1] == true;
        var prefix := my_syndrome[0..i];
        assert |prefix| > 0;
        assert prefix[|prefix|-1] == true;
        assert countTrue(prefix) == 1 + countTrue(prefix[0..|prefix|-1]);
        assert my_syndrome[0..i-1] == prefix[0..|prefix|-1];
    }
}
}