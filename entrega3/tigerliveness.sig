signature tigerliveness =
sig
  datatype igraph = IGRAPH of {graph : tigergraph.graph,
                              tnode : tigertemp.temp -> tigergraph.node,
                              gtemp : tigergraph.node -> tigertemp.temp,
                              moves : (tigergraph.node * tigergraph.node) list}

  (*val inteferenceGraph : tigerflowgraph.flowgraph -> igraph * (tigergraph.node -> tigertemp.temp list) *)

end
