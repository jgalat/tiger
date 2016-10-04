signature tigerflowgraph =
sig
  type flowgraph
  val makeGraph: tigerassem.instr list -> (flowgraph * tigergraph.node list)
end
