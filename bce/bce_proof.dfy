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

        // Prove that my own computed syndrome is good
        var my_syndrome := syndromes_received[node.id]; // syndome computed by node.id for itself
        assert node == s'.nodes[node.id];
        assert my_syndrome == computeSyndrome(node);
        lemma_Computed_Syndromes_Have_Length_n(node, my_syndrome);
        lemma_BCE_Validity_Correct_Nodes_Own_Syndrome_Is_Good(node, my_syndrome);
        assert countTrue(my_syndrome) >= node.n - node.f;

        // Prove that n-f of received syndromes are good
        assert forall i :: 0 <= i < s'.n ==> syndromes_received[i] == computeSyndrome(s'.nodes[i]);
        lemma_BCE_Validity_CountGoodSyndromes_Succeeds(s', node, syndromes_received);
    }
}


/* Prove that for any non-faulty node n, countTrue(computeSyndrome(n)) >= n - f */
// TODO
lemma lemma_BCE_Validity_Correct_Nodes_Send_Good_Syndrome(s':Service, node: Node, syndromes_received: seq<syndrome>) 
    requires node_invariants(s');
    requires |s'.nodes| == s'.n;
    requires forall  i :: 0 <= i < s'.n ==> s'.nodes[i].id == i
    requires node in s'.nodes;
    requires forall n :: n in s'.nodes ==> n.n == |n.symbols| == |n.codeword|;
    // requires forall node :: 
    //     node in s'.nodes && !node.faulty
    //     ==>
    //     && node.symbols == node.codeword  //by "everyone is behaving" temporary assumption
    //     && node.state == Phase2
    //     && 0 <= node.id < s'.n
    requires |syndromesToExchange(s'.nodes)| == s'.n;
    requires syndromes_received == syndromesToExchange(s'.nodes)[node.id];
    requires |syndromes_received| == s'.n;
    requires forall i :: 0 <= i < s'.n ==> syndromes_received[i] == computeSyndrome(s'.nodes[i]);
    ensures forall id :: 0 <= id < s'.n 
        ==> 
        (!s'.nodes[id].faulty ==> countTrue(computeSyndrome(s'.nodes[id])) >= node.n - node.f);
{}


// TODO
lemma {:induction syndromes_received} lemma_BCE_Validity_CountGoodSyndromes_Succeeds(s':Service, node: Node, syndromes_received: seq<syndrome>) 
    requires node_invariants(s');
    requires |s'.nodes| == s'.n;
    requires forall  i :: 0 <= i < s'.n ==> s'.nodes[i].id == i
    requires node in s'.nodes;
    requires forall n :: n in s'.nodes ==> n.n == |n.symbols| == |n.codeword|;
    // requires forall node :: 
    //     node in s'.nodes && !node.faulty
    //     ==>
    //     && node.symbols == node.codeword  //by "everyone is behaving" temporary assumption
    //     && node.state == Phase2
    //     && 0 <= node.id < s'.n
    requires |syndromesToExchange(s'.nodes)| == s'.n;
    requires syndromes_received == syndromesToExchange(s'.nodes)[node.id];
    requires |syndromes_received| == s'.n;
    requires forall i :: 0 <= i < s'.n ==> syndromes_received[i] == computeSyndrome(s'.nodes[i]);
    ensures countGoodSyndromes(syndromes_received, node.n-node.f) >= s'.n - s'.f;
{
    lemma_BCE_Validity_Correct_Nodes_Send_Good_Syndrome(s', node, syndromes_received);
    lemma_BCE_Validity_CountGoodSyndromes_Succeeds_Helper(s', node, syndromes_received, s'.n, s'.f);
}


// TODO
lemma {:induction i, f} lemma_BCE_Validity_CountGoodSyndromes_Succeeds_Helper(s':Service, node: Node, syndromes_received: seq<syndrome>, i: int, f: int) 
    decreases i, f;
    requires node_invariants(s');
    requires 0 <= i <= s'.n;
    requires 0 <= f <= s'.f;
    requires |s'.nodes| == s'.n;
    requires forall  id :: 0 <= id < s'.n ==> s'.nodes[id].id == id
    requires node in s'.nodes;
    requires forall n :: n in s'.nodes ==> n.n == |n.symbols| == |n.codeword|;
    requires |syndromesToExchange(s'.nodes)| == s'.n;
    requires syndromes_received == syndromesToExchange(s'.nodes)[node.id];
    requires |syndromes_received| == s'.n;
    requires forall id :: 0 <= id < s'.n ==> syndromes_received[id] == computeSyndrome(s'.nodes[id]);
    requires forall id :: 0 <= id < s'.n ==> 
        (!s'.nodes[id].faulty ==> countTrue(computeSyndrome(s'.nodes[id])) >= s'.n - s'.f)
    ensures countGoodSyndromes(syndromes_received[..i], node.n-node.f) >= i - f;
{
    var thresh := s'.n - s'.f;
    if i == 0 {
        assert countGoodSyndromes(syndromes_received[..i], thresh) == 0;
    } else {
        // Check the next syndrome (ith) for goodness
        if !s'.nodes[i-1].faulty {
            lemma_BCE_Validity_CountGoodSyndromes_Succeeds_Helper(s', node, syndromes_received, i-1, f);
            var check_prefix := syndromes_received[..i];
            var x := countTrue(check_prefix[|check_prefix|-1]);
            assert x >= thresh;
            assert countGoodSyndromes(check_prefix, thresh) ==
                1 + countGoodSyndromes(check_prefix[..|check_prefix|-1], thresh);
            assert check_prefix[..|check_prefix|-1] == syndromes_received[..i-1];
        } else {
            if f > 0 {
                lemma_BCE_Validity_CountGoodSyndromes_Succeeds_Helper(s', node, syndromes_received, i-1, f-1);
                var check_prefix := syndromes_received[..i];
                var x := countTrue(check_prefix[|check_prefix|-1]);
                if x >= thresh {
                    assert countGoodSyndromes(check_prefix, thresh) ==
                        1 + countGoodSyndromes(check_prefix[..|check_prefix|-1], thresh);
                    assert check_prefix[..|check_prefix|-1] == syndromes_received[..i-1];
                } else {
                    assert countGoodSyndromes(check_prefix, thresh) == countGoodSyndromes(check_prefix[..|check_prefix|-1], thresh);
                    assert check_prefix[..|check_prefix|-1] == syndromes_received[..i-1];
                }
            } else {
                // Every node seen must be correct from this point
                lemma_BCE_Validity_CountGoodSyndromes_Succeeds_Helper(s', node, syndromes_received, i-1, f);
                var check_prefix := syndromes_received[..i];
                assert !s'.nodes[i-1].faulty;
                var x := countTrue(check_prefix[|check_prefix|-1]);
                assert x >= thresh;
                assert countGoodSyndromes(check_prefix, thresh) ==
                    1 + countGoodSyndromes(check_prefix[..|check_prefix|-1], thresh);
                assert check_prefix[..|check_prefix|-1] == syndromes_received[..i-1];
            }
        }
    }
}


/* Prove that for any correct node, its own syndrome has n-f 'true' bits */
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
    assert my_syndrome[..node.n] == my_syndrome;
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
    ensures countTrue(my_syndrome[..i]) >= i - node.f;
{
    if i == 0 {
        assert my_syndrome[..i] == [];
        assert countTrue(my_syndrome[..i]) == 0;
    } else {
        lemma_BCE_Validity_Correct_Nodes_Own_Syndrome_Is_Good_Helper(node, my_syndrome, i-1);
        assert countTrue(my_syndrome[..i-1]) >= i-1 - node.f;
        assert node.symbols[i-1] == node.codeword[i-1];
        lemma_Computed_Syndromes_Is_Correct(node, my_syndrome);
        assert my_syndrome[i-1] == true;
        var prefix := my_syndrome[..i];
        assert |prefix| > 0;
        assert prefix[|prefix|-1] == true;
        assert countTrue(prefix) == 1 + countTrue(prefix[..|prefix|-1]);
        assert my_syndrome[..i-1] == prefix[..|prefix|-1];
    }
}
}