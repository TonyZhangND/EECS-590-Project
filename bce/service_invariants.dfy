include "service.dfy"
include "node.dfy"

module Service_Invariants {
import opened BCE_Protocol_Service
import opened BCE_Protocol_Node


/****************************************************************************************/
/*                              AUXILIARY FUNCTIONS                                     */
/****************************************************************************************/ 


/* Maps nodes to the number of faulty nodes in the seq */
function countFaulty(nodes: seq<Node>) : int
    decreases nodes;
{
    if |nodes| == 0 then 0 else (
        if nodes[|nodes|-1].faulty then 1 + countFaulty(nodes[..|nodes|-1]) else countFaulty(nodes[..|nodes|-1])
    )
}

lemma lemma_Count_Faulty_Increment_Property(nodes: seq<Node>, i: int) 
    decreases nodes;
    requires 0 < i <= |nodes|;
    ensures !nodes[i-1].faulty ==> countFaulty(nodes[..i]) == countFaulty(nodes[..i-1]);
    ensures nodes[i-1].faulty ==> countFaulty(nodes[..i-1]) == countFaulty(nodes[..i]) - 1;
{
    var nodes_prefix := nodes[..i];
    if !nodes[i-1].faulty {
        assert countFaulty(nodes_prefix) == countFaulty(nodes_prefix[..|nodes_prefix|-1]);
    } else {
        assert countFaulty(nodes_prefix) == countFaulty(nodes_prefix[..|nodes_prefix|-1]) + 1;
    }
    assert nodes_prefix[..|nodes_prefix|-1] == nodes[..i-1];
}

/* Proof that countFaulty(nodes) cannot give a negative number */
lemma {:induction nodes} lemma_Count_Faulty_Non_Negative_Property (nodes: seq<Node>) 
    ensures countFaulty(nodes) >= 0;
{}

/* Proof that countFaulty(nodes) exceed length of list */
lemma {:induction nodes} lemma_Count_Faulty_Upper_Bound_Property (nodes: seq<Node>) 
    ensures countFaulty(nodes) <= |nodes|;
{}

/* Proof that countFaulty(nodes) only depends on the node.faulty field of each node */
lemma {:induction nodes1, nodes2} lemma_Count_Faulty_Identity_Property (nodes1: seq<Node>, nodes2: seq<Node>) 
    requires |nodes1| == |nodes2|;
    requires forall i :: 0 <= i < |nodes1| ==> nodes1[i].faulty == nodes2[i].faulty;
    ensures countFaulty(nodes1) == countFaulty(nodes2);
{}


/****************************************************************************************/
/*                                     INVARIANTS                                       */
/****************************************************************************************/ 


predicate node_invariants(s: Service)
{
    forall node :: node in s.nodes ==>
    && node.n == node.f * 3 + 1
    && 0 <= node.id < node.n
    && 0 <= node.id < node.n
    && node.n == s.n
    && node.f == s.f
    && |node.codeword| == node.n
    && node.faulty == (node.id < node.f)
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
    && node_faultiness_count_invariant(s, s', s'')
    // id of each node is constant
    && node_identity_invariant(s, s', s'')
}

// Number of nodes is constant
predicate node_membership_invariant(s:Service, s':Service, s'':Service)
{
    && |s.nodes| == |s'.nodes| == |s''.nodes| == s.n
    && s.n == s'.n == s''.n
}

// Correctness of each node is constant and the first f nodes are faulty
predicate node_faultiness_invariant(s:Service, s':Service, s'':Service) 
    requires node_membership_invariant(s, s', s'');
{
    && s.f == s'.f == s''.f
    && (forall id :: 0 <= id < s.n ==> s.nodes[id].faulty == (id < s.f))
    && (forall  id :: 0 <= id < s.n ==> s.nodes[id].faulty == s'.nodes[id].faulty == s''.nodes[id].faulty)
}

// At most f nodes are faulty at any time
predicate node_faultiness_count_invariant(s:Service, s':Service, s'':Service) 
    requires node_membership_invariant(s, s', s'');
{
    && countFaulty(s.nodes) <= s.f
    && countFaulty(s'.nodes) <= s'.f
    && countFaulty(s''.nodes) <= s''.f
}

// Identity of each node is constant
predicate node_identity_invariant(s:Service, s':Service, s'':Service)
    requires node_membership_invariant(s, s', s'');
{
    forall  i :: 0 <= i < s.n 
    ==> 
    && s.nodes[i].id == i
    && s'.nodes[i].id == i
    && s''.nodes[i].id == i
}


/****************************************************************************************/
/*                                       PROOFS                                         */
/****************************************************************************************/ 

lemma lemma_Service_Maintains_Invariants(s:Service, s':Service, s'':Service) 
    requires BCE(s, s', s'');
    ensures service_invariants(s, s', s'');
{
    lemma_Node_Faultiness_Count_Invariant(s);
    assert node_faultiness_invariant(s, s', s'');
    lemma_Count_Faulty_Identity_Property(s.nodes,s'.nodes);
    lemma_Count_Faulty_Identity_Property(s.nodes,s''.nodes);
}

/* Prove that in the initial state, countFaulty <= f */
lemma lemma_Node_Faultiness_Count_Invariant(s:Service)
    requires serviceInit(s);
    ensures countFaulty(s.nodes) <= s.f;
{
    assert forall id :: 0 <= id < |s.nodes| ==> nodeInit(s.nodes[id], s.f, s.n, id);
    assert forall id :: 0 <= id < s.n ==> (s.nodes[id].faulty <==> id < s.f);

    lemma_Node_Faultiness_Count_Invariant_Helper(s.nodes, s.f, s.n);
    assert s.nodes[..s.n] == s.nodes;
}

lemma {:induction i} lemma_Node_Faultiness_Count_Invariant_Helper(nodes: seq<Node>, f:int, i:int) 
    requires forall id :: 0 <= id < |nodes| ==> (nodes[id].faulty <==> id < f)
    requires 0 <= f <= |nodes|;
    requires 0 <= i <= |nodes|;
    ensures i <= f ==> countFaulty(nodes[..i]) <= i;
    ensures i > f ==> countFaulty(nodes[..i]) <= f;
{
    if i <= f {
        assert |nodes[..i]| <= f;
        lemma_Count_Faulty_Upper_Bound_Property(nodes[..i]);
    } else {
        lemma_Node_Faultiness_Count_Upper_Bound(nodes, f, i);
    }
} 

/* Prove that for i >= f, countFaulty(nodes[..i]) = countFaulty(nodes[..f]) */
lemma {:induction i} lemma_Node_Faultiness_Count_Upper_Bound(nodes: seq<Node>, f:int, i:int) 
    decreases i;
    requires forall id :: 0 <= id < |nodes| ==> (nodes[id].faulty <==> id < f)
    requires 0 <= f <= |nodes|;
    requires f < i <= |nodes|;
    ensures i > f ==> countFaulty(nodes[..i]) == countFaulty(nodes[..f]);
{
    if i == f {
        assert countFaulty(nodes[..i]) == countFaulty(nodes[..f]);
    } else {
        assert !nodes[i-1].faulty;
        lemma_Count_Faulty_Increment_Property(nodes, i);
    }
} 
}
