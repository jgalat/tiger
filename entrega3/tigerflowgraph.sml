structure tigerflowgraph :> tigerflowgraph =
struct
    open tigergraph
    open tigerassem
    open Splayset
    open Splaymap
    open tigertab

    datatype flowgraph = FGRAPH of {control: graph,
                                    def: tigertemp.temp set nodeDict,
                                    use: tigertemp.temp set nodeDict,
                                    ismove: bool nodeDict}

  (* Note:  any "use" within the block is assumed to be BEFORE a "def"
        of the same variable.  If there is a def(x) followed by use(x)
       in the same block, do not mention the use in this data structure,
       mention only the def.

     More generally:
       If there are any nonzero number of defs, mention def(x).
       If there are any nonzero number of uses BEFORE THE FIRST DEF,
           mention use(x).

     For any node in the graph,
           Graph.Table.look(def,node) = SOME(def-list)
           Graph.Table.look(use,node) = SOME(use-list)
   *)

end
