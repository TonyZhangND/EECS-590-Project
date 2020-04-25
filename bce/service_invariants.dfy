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
/*                                       LEMMAS                                         */
/****************************************************************************************/ 

lemma lemma_Service_Maintains_Invariants(s:Service, s':Service, s'':Service) 
    requires BCE(s, s', s'');
    ensures service_invariants(s, s', s'');
{

    // TODO
    assert countFaulty(s.nodes) <= s.f;
    assert countFaulty(s'.nodes) <= s'.f;
    assert countFaulty(s''.nodes) <= s''.f;
}
}
