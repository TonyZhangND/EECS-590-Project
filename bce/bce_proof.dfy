include "service.dfy"
include "node.dfy"

module BCE_Proof {
import opened BCE_Protocol_Service
import opened BCE_Protocol_Node


lemma lemma_BCE_Equivalence(s:Service, s':Service, s'':Service) 
    requires BCE(s, s', s'');
    ensures forall node :: 
        node in s''.nodes && !node.faulty && node.decision != Bottom 
        ==> 
        node.decision == Codeword;
{}

lemma lemma_BCE_Termination(s:Service, s':Service, s'':Service) 
    requires BCE(s, s', s'');
    ensures forall node :: 
        node in s''.nodes && !node.faulty 
        ==> 
        (node.decision == Codeword || node.decision == Bottom);
{}

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

lemma lemma_BCE_Validity_Correct_Nodes_Decide_Codeword(s':Service, syndromes: seq<seq<syndrome>>) 
    requires forall node :: 
        && node in s'.nodes && !node.faulty
        ==>
        node.symbols == node.codeword;
    ensures forall node :: node in s'.nodes && !node.faulty ==> decideOnCodeWord(node, syndromes[node.id]);
{}
}