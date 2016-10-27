signature tigergraph =
sig
    type graph
    type node

    val nodes: graph -> node list
    val succ: node -> node list
    val pred: node -> node list
    val adj: node -> node list   (* succ+pred *)
    val degree: node -> int
    val areAdj : node -> node -> bool
    val eq: node*node -> bool
    val cmpNode: node * node -> order

    val newGraph: unit -> graph
    val newNode : graph -> node
    exception GraphEdge
    val mk_edge: {from: node, to: node} -> unit
    val rm_edge: {from: node, to: node} -> unit

    type 'a nodeDict = (node , 'a) Splaymap.dict

    val nodename: node->string  (* for debugging only *)

end
