structure tigerliveness :> tigerliveness =
struct
  datatype igraph = IGRAPH of {graph : tigergraph.graph,
                              tnode : tigertemp.temp -> tigergraph.node,
                              gtemp : tigergraph.node -> tigertemp.temp,
                              moves : (tigergraph.node * tigergraph.node) list}

  (* fun inteferenceGraph fg = *)


end
