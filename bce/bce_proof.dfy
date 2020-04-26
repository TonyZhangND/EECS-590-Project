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

/* Main Validity proof */
lemma lemma_BCE_Validity(s:Service, s':Service, s'':Service) 
    requires BCE(s, s', s'');
    // Validity assumption
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
    assert forall node :: 
        && node in s'.nodes && !node.faulty
        ==>
        && countSame(node.codeword, node.symbols) >= s'.n - s'.f;
    lemma_BCE_Validity_Correct_Nodes_Send_Good_Syndrome(s'); 
    var syndromes := syndromesToExchange(s'.nodes);
    lemma_Exchanged_Syndromes_Are_Extracted(s'.nodes);
    forall node | node in s'.nodes && !node.faulty  
    ensures forall syn :: syn in syndromes[node.id] ==> |syn| == s'.n
    {
        assert syndromes[node.id] == extractSyndromes(s'.nodes);
        lemma_Extract_Generates_One_Syndrome_For_Each_Node(s'.nodes);
        assert forall i :: 0 <= i < |s'.nodes| ==> syndromes[node.id][i] == computeSyndrome(s'.nodes[i]);
    }
    assert forall node :: node in s'.nodes && !node.faulty ==>
        (forall syn :: syn in syndromes[node.id] ==> |syn| == s'.n);
    lemma_BCE_Validity_Correct_Nodes_Decide_Codeword(s', syndromes);
}


lemma lemma_BCE_Validity_Receive_n_f_Common_Symbols(s:Service, s':Service) 
    // Validity assumption
    requires forall node1, node2 :: 
            && node1 in s.nodes && node2 in s.nodes 
            && !node1.faulty && !node2.faulty ==> 
            node1.codeword == node2.codeword;
    // Boilerplate stuff
    requires serviceInit(s);
    requires countFaulty(s'.nodes) <= s'.f;
    requires serviceExchangeSymbols(s, s');
    requires node_invariants(s');
    // Behavior of faulty node, for convinience
    ensures forall node :: 
        && node in s'.nodes && node.faulty
        ==>
        |node.symbols| == |node.codeword|;
    // Behavior of correct node
    ensures forall i :: 
        0 <= i < s'.n && !s'.nodes[i].faulty
        ==>
        |s'.nodes[i].codeword| == |s'.nodes[i].symbols|
        && countSame(s'.nodes[i].codeword, s'.nodes[i].symbols) >= s'.n - s'.f
{
    lemma_Exchange_Generates_One_SymbolSeq_For_Each_Node(s.nodes, 0);
    assert forall i :: 0 <= i < s.n ==> s'.nodes[i].symbols == symbolsToExchange(s.nodes)[i];
    lemma_Exchanged_Symbols_Are_Extracted(s.nodes);

    forall i | 0 <= i < s'.n && !s'.nodes[i].faulty
    ensures 
        && |s'.nodes[i].symbols| == |s'.nodes[i].codeword|
        && countSame(s'.nodes[i].codeword, s'.nodes[i].symbols) >= s'.n - s'.f
    {
        var node := s'.nodes[i];
        assert node.symbols == symbolsToExchange(s.nodes)[i] == extractSymbols(s.nodes);
        lemma_Extract_Takes_ith_Symbol_From_Node_i(s.nodes);
        assert forall k :: 0 <= k < s'.n && !s.nodes[k].faulty 
            ==> node.symbols[k] == s.nodes[k].codeword[k] == node.codeword[k];
        assert countFaulty(s'.nodes) <= s'.f;      
        lemma_CountSame_Complements_CountFaulty(s'.nodes, node, s'.f);
        assert |s'.nodes| == s'.n;
    }
}


/* Prove that if countFaulty(nodes) <= f, then 
* countSame(node.codeword, node.symbols) >= |nodes| - f */
lemma {:induction nodes} lemma_CountSame_Complements_CountFaulty(nodes: seq<Node>, node: Node, f: int) 
    requires |nodes| > 0;
    requires |node.symbols| == |node.codeword| == |nodes|;
    requires forall n :: n in nodes ==> |n.codeword| == |nodes|;
    requires countFaulty(nodes) <= f;
    requires forall k :: 0 <= k < |nodes| && !nodes[k].faulty 
            ==> node.symbols[k] == nodes[k].codeword[k] == node.codeword[k];
    ensures countSame(node.codeword, node.symbols) >= |nodes| - f;
{
    var n := |nodes|;
    assert n > 0;
    lemma_Count_Faulty_Increment_Property(nodes, n);
    lemma_CountSame_Complements_CountFaulty_Helper(nodes, node, f, n);
    assert node.codeword[..n] == node.codeword;
    assert node.symbols[..n] == node.symbols;
}


lemma {:induction f, i} lemma_CountSame_Complements_CountFaulty_Helper(nodes: seq<Node>, node: Node, f: int, i: int)
    decreases f, i;
    requires 0 <= i <= |nodes|;
    requires |node.symbols| == |node.codeword| == |nodes|;
    requires forall n :: n in nodes ==> |n.codeword| == |nodes|;
    requires countFaulty(nodes[..i]) <= f;
    requires forall k :: 0 <= k < |nodes| && !nodes[k].faulty 
            ==> node.symbols[k] == nodes[k].codeword[k] == node.codeword[k];
    ensures countSame(node.codeword[..i], node.symbols[..i]) >= i - f;
{
    if i == 0 {
        assert countSame(node.codeword[..i], node.symbols[..i]) == 0;
    } else {
        if !nodes[i-1].faulty {
            lemma_Count_Faulty_Increment_Property(nodes, i);
            lemma_CountSame_Complements_CountFaulty_Helper(nodes, node, f, i-1);
            assert node.symbols[i-1] == node.codeword[i-1];
            lemma_CountSame_Increment_Property(node.codeword, node.symbols, i);
        } else {
            if f > 0 {
                lemma_Count_Faulty_Increment_Property(nodes, i);
                lemma_CountSame_Complements_CountFaulty_Helper(nodes, node, f-1, i-1);
                lemma_CountSame_Increment_Property(node.codeword, node.symbols, i);
            } else {
                lemma_Count_Faulty_Increment_Property(nodes, i);
                assert countFaulty(nodes[..i-1]) < 0;
                lemma_Count_Faulty_Non_Negative_Property(nodes[..i-1]);
                assert false;
            }
        }
    }
}



/* Prove that for any non-faulty node n, countTrue(computeSyndrome(n)) >= n - f */
lemma lemma_BCE_Validity_Correct_Nodes_Send_Good_Syndrome(s':Service) 
    // Validity assumption
    requires forall node1, node2 :: 
            && node1 in s'.nodes && node2 in s'.nodes 
            && !node1.faulty && !node2.faulty ==> 
            node1.codeword == node2.codeword;
    // Boilerplate stuff 
    requires node_invariants(s');
    requires |s'.nodes| == s'.n;
    requires forall  i :: 0 <= i < s'.n ==> s'.nodes[i].id == i
    requires forall n :: n in s'.nodes && !n.faulty ==> n.n == |n.symbols| == |n.codeword|;
    requires forall node :: 
        node in s'.nodes && !node.faulty
        ==>
        && node.state == Phase2
        && 0 <= node.id < s'.n
    // Facts needed for this proof
    requires forall node :: 
        && node in s'.nodes && !node.faulty
        ==>
        && countSame(node.codeword, node.symbols) >= s'.n - s'.f;
    ensures forall id :: 0 <= id < s'.n 
        ==> 
        (!s'.nodes[id].faulty ==> countTrue(computeSyndrome(s'.nodes[id])) >= s'.n - s'.f);
{
    forall id | 0 <= id < s'.n && !s'.nodes[id].faulty
    ensures countTrue(computeSyndrome(s'.nodes[id])) >= s'.n - s'.f
    {
        var node := s'.nodes[id];
        assert countSame(node.codeword, node.symbols)>= s'.n - s'.f;
        lemma_CountTrue_Equals_CountSame(node);
    }
}


/* Prove that all correct nodes will decide on the codeword */
lemma lemma_BCE_Validity_Correct_Nodes_Decide_Codeword(s':Service, syndromes: seq<seq<syndrome>>) 
    // Validity assumption
    requires forall node1, node2 :: 
            && node1 in s'.nodes && node2 in s'.nodes 
            && !node1.faulty && !node2.faulty ==> 
            node1.codeword == node2.codeword;
    // Boilerplate stuff
    requires node_invariants(s');
    requires |s'.nodes| == s'.n;
    requires forall  i :: 0 <= i < s'.n ==> s'.nodes[i].id == i
    requires forall node :: node in s'.nodes ==> node.n == |node.symbols| == |node.codeword|;
    requires syndromes == syndromesToExchange(s'.nodes);
    requires |syndromes| == s'.n;
    requires countFaulty(s'.nodes) <= s'.f;
    requires forall nd :: 
        nd in s'.nodes && !nd.faulty
        ==>
        && nd.state == Phase2
        && 0 <= nd.id < s'.n
        && 0 <= nd.id < |syndromes[nd.id]|;
    requires forall node :: node in s'.nodes && !node.faulty ==>
        (forall syn :: syn in syndromes[node.id] ==> |syn| == s'.n);
    // Facts needed for this proof
    requires forall id :: 0 <= id < s'.n 
        ==> 
        (!s'.nodes[id].faulty ==> countTrue(computeSyndrome(s'.nodes[id])) >= s'.n - s'.f);
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
        // lemma_BCE_Validity_Correct_Nodes_Own_Syndrome_Is_Good(node, my_syndrome);
        assert countTrue(my_syndrome) >= node.n - node.f;

        // Prove that n-f of received syndromes are good
        // TODO
        assert exists goodSet : multiset<syndrome> :: (
            && goodSet <= multiset(syndromes_received) 
            && goodSyndromeSet(goodSet, s'.n, s'.n-s'.f)
        );
    }
}



/* Prove that if node is correct, then countGoodSyndromes will give a count >= n-f */
// lemma {:induction syndromes_received} lemma_BCE_Validity_CountGoodSyndromes_Succeeds(s':Service, node: Node, syndromes_received: seq<syndrome>) 
//     // Boilerplate stuff
//     requires node_invariants(s');
//     requires |s'.nodes| == s'.n;
//     requires forall  i :: 0 <= i < s'.n ==> s'.nodes[i].id == i
//     requires node in s'.nodes;
//     requires forall n :: n in s'.nodes ==> n.n == |n.symbols| == |n.codeword|;
//     requires |syndromesToExchange(s'.nodes)| == s'.n;
//     requires syndromes_received == syndromesToExchange(s'.nodes)[node.id];
//     requires |syndromes_received| == s'.n;
//     requires forall i :: 0 <= i < s'.n ==> syndromes_received[i] == computeSyndrome(s'.nodes[i]);
//     requires forall nd :: 
//         nd in s'.nodes && !nd.faulty
//         ==>
//         && nd.state == Phase2
//         && 0 <= nd.id < s'.n
//     // Facts needed for this proof
//     requires forall id :: 0 <= id < s'.n 
//         ==> 
//         (!s'.nodes[id].faulty ==> countTrue(computeSyndrome(s'.nodes[id])) >= s'.n - s'.f);
//     requires forall node1, node2 :: 
//             && node1 in s'.nodes && node2 in s'.nodes 
//             && !node1.faulty && !node2.faulty ==> 
//             node1.codeword == node2.codeword;
//     requires countFaulty(s'.nodes) <= s'.f;
//     ensures countGoodSyndromes(syndromes_received, node.n-node.f) >= s'.n - s'.f;
// {
//     assert s'.nodes[..s'.n] == s'.nodes;
//     assert countFaulty(s'.nodes[..s'.n]) <= s'.f;
//     lemma_BCE_Validity_CountGoodSyndromes_Succeeds_Helper(s', node, syndromes_received, s'.n, s'.f);
//     assert syndromes_received[..s'.n] == syndromes_received;
// }


// lemma {:induction i, f} lemma_BCE_Validity_CountGoodSyndromes_Succeeds_Helper(s':Service, node: Node, syndromes_received: seq<syndrome>, i: int, f: int) 
//     decreases i, f;
//     // Boilerplate stuff
//     requires node_invariants(s');
//     requires |s'.nodes| == s'.n;
//     requires forall  id :: 0 <= id < s'.n ==> s'.nodes[id].id == id
//     requires node in s'.nodes;
//     requires forall n :: n in s'.nodes ==> n.n == |n.symbols| == |n.codeword|;
//     requires |syndromesToExchange(s'.nodes)| == s'.n;
//     requires syndromes_received == syndromesToExchange(s'.nodes)[node.id];
//     requires |syndromes_received| == s'.n;
//     requires forall id :: 0 <= id < s'.n ==> syndromes_received[id] == computeSyndrome(s'.nodes[id]);
//     // Facts needed for this proof
//     requires forall id :: 0 <= id < s'.n ==> 
//         (!s'.nodes[id].faulty ==> countTrue(computeSyndrome(s'.nodes[id])) >= s'.n - s'.f)
//     requires 0 <= i <= s'.n;
//     requires 0 <= f <= s'.f;
//     requires countFaulty(s'.nodes[..i]) <= f;
//     ensures countGoodSyndromes(syndromes_received[..i], node.n-node.f) >= i - f;
// {
//     var thresh := s'.n - s'.f;
//     if i == 0 {
//         assert countGoodSyndromes(syndromes_received[..i], thresh) == 0;
//     } else { // Check the next syndrome (ith) for goodness
//         if !s'.nodes[i-1].faulty {
//             // If node is correct:
//             // Check countFaulty
//             lemma_Count_Faulty_Increment_Property(s'.nodes, i);

//             // Invoke induction hypothesis
//             lemma_BCE_Validity_CountGoodSyndromes_Succeeds_Helper(s', node, syndromes_received, i-1, f);

//             // Check countGoodSyndromes
//             var check_prefix := syndromes_received[..i];
//             var x := countTrue(check_prefix[|check_prefix|-1]);
//             assert x >= thresh;
//             assert countGoodSyndromes(check_prefix, thresh) ==
//                 1 + countGoodSyndromes(check_prefix[..|check_prefix|-1], thresh);
//             assert check_prefix[..|check_prefix|-1] == syndromes_received[..i-1];
//         } else {
//             // If node is faulty:
//             if f > 0 {
//                 // Check countFaulty
//                 lemma_Count_Faulty_Increment_Property(s'.nodes, i);
//                 assert countFaulty(s'.nodes[..i-1]) == countFaulty(s'.nodes[..i]) - 1;

//                 // Invoke induction hypothesis
//                 lemma_BCE_Validity_CountGoodSyndromes_Succeeds_Helper(s', node, syndromes_received, i-1, f-1);

//                 // Check countGoodSyndromes
//                 var check_prefix := syndromes_received[..i];
//                 var x := countTrue(check_prefix[|check_prefix|-1]);
//                 if x >= thresh {
//                     assert countGoodSyndromes(check_prefix, thresh) ==
//                         1 + countGoodSyndromes(check_prefix[..|check_prefix|-1], thresh);
//                     assert check_prefix[..|check_prefix|-1] == syndromes_received[..i-1];
//                 } else {
//                     assert countGoodSyndromes(check_prefix, thresh) == countGoodSyndromes(check_prefix[..|check_prefix|-1], thresh);
//                     assert check_prefix[..|check_prefix|-1] == syndromes_received[..i-1];
//                 }
//             } else {
//                 // f=0, so every node seen must be correct from this point. 
//                 if !s'.nodes[i-1].faulty {
//                     lemma_BCE_Validity_CountGoodSyndromes_Succeeds_Helper(s', node, syndromes_received, i-1, f);
//                     var check_prefix := syndromes_received[..i];
//                     var x := countTrue(check_prefix[|check_prefix|-1]);
//                     assert x >= thresh;
//                     assert countGoodSyndromes(check_prefix, thresh) ==
//                         1 + countGoodSyndromes(check_prefix[..|check_prefix|-1], thresh);
//                     assert check_prefix[..|check_prefix|-1] == syndromes_received[..i-1];
//                 } else {
//                     // Proof by contradiction that s'.nodes[i-1] cannot be faulty
//                     assert f == 0;
//                     assert countFaulty(s'.nodes[..i]) <= f;
//                     lemma_Count_Faulty_Increment_Property(s'.nodes, i);
//                     assert countFaulty(s'.nodes[..i-1]) < 0;
//                     lemma_Count_Faulty_Non_Negative_Property(s'.nodes[..i-1]);
//                     assert false; // Contradiction!
//                 }
//             }
//         }
//     }
// }


/* Prove that for any correct node, its own syndrome has n-f 'true' bits */
// lemma {:induction my_syndrome} lemma_BCE_Validity_Correct_Nodes_Own_Syndrome_Is_Good(node: Node, my_syndrome: syndrome) 
//     requires !node.faulty;
//     requires node.state == Phase2;
//     requires |my_syndrome| == node.n;
//     requires node.n == 3 * node.f + 1
//     requires node.n == |node.symbols| == |node.codeword|; 
//     requires node.symbols == node.codeword; //by "everyone is behaving" temporary assumption
//     requires my_syndrome == computeSyndrome(node);
//     ensures countTrue(my_syndrome) >= node.n - node.f;
// {
//     assert |computeSyndrome(node)| == node.n;
//     assert my_syndrome[..node.n] == my_syndrome;
//     lemma_BCE_Validity_Correct_Nodes_Own_Syndrome_Is_Good_Helper(node, my_syndrome, node.n);
// }


// lemma {:induction i} lemma_BCE_Validity_Correct_Nodes_Own_Syndrome_Is_Good_Helper(node: Node, my_syndrome: syndrome, i: int) 
//     decreases i;
//     requires !node.faulty;
//     requires node.state == Phase2;
//     requires |my_syndrome| == node.n;
//     requires node.n == 3 * node.f + 1
//     requires node.n == |node.symbols| == |node.codeword|; 
//     requires node.symbols == node.codeword; //by "everyone is behaving" temporary assumption
//     requires my_syndrome == computeSyndrome(node);
//     requires 0 <= i <= node.n;
//     ensures countTrue(my_syndrome[..i]) >= i - node.f;
// {
//     if i == 0 {
//         assert my_syndrome[..i] == [];
//         assert countTrue(my_syndrome[..i]) == 0;
//     } else {
//         lemma_BCE_Validity_Correct_Nodes_Own_Syndrome_Is_Good_Helper(node, my_syndrome, i-1);
//         assert countTrue(my_syndrome[..i-1]) >= i-1 - node.f;
//         assert node.symbols[i-1] == node.codeword[i-1];
//         lemma_Computed_Syndromes_Is_Correct(node, my_syndrome);
//         assert my_syndrome[i-1] == true;
//         var prefix := my_syndrome[..i];
//         assert |prefix| > 0;
//         assert prefix[|prefix|-1] == true;
//         assert countTrue(prefix) == 1 + countTrue(prefix[..|prefix|-1]);
//         assert my_syndrome[..i-1] == prefix[..|prefix|-1];
//     }
// }
}