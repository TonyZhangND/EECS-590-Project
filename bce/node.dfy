module BCE_Protocol_Node {

datatype NodeState = Phase1 | Phase2 | Decided

datatype Node = Node(
    input: seq<nat>,
    state: NodeState
)

predicate Node_Init(s: Node)
{
    // TODO
    true
}

predicate Node_Next(s:Node, s':Node)
{
    // TODO
    true
}
    
}