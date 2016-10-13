signature tigerflowgraph =
sig

  datatype flowgraph = FGRAPH of {control: tigergraph.graph,
                                  def: tigertemp.temp Splayset.set tigergraph.nodeDict,
                                  use: tigertemp.temp Splayset.set tigergraph.nodeDict,
                                  ismove: bool tigergraph.nodeDict }

  val makeGraph: tigerassem.instr list -> (flowgraph * tigergraph.node list)
end
