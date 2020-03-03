include "node.dfy"

module BCE_Protocol_Service {
import opened BCE_Protocol_Node


datatype ServiceState = ServiceState(
    nodes:set<Node>
)

predicate Service_Init(s: ServiceState)
{
    // TODO
    true
}

predicate Service_Next(s:ServiceState, s':ServiceState)
{
    // TODO
    true
}


}