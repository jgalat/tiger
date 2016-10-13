structure tigerliveness :> tigerliveness =
struct

  open Splayset
  open Splaymap
  open tigergraph
  open tigerflowgraph

  datatype igraph = IGRAPH of {graph : tigergraph.graph,
                              tnode : tigertemp.temp -> tigergraph.node,
                              gtemp : tigergraph.node -> tigertemp.temp,
                              moves : (tigergraph.node * tigergraph.node) list}

  fun liveAnalysis (FGRAPH {control, def, use, ismove}) =
    let
      fun defF n = find (def, n)
      fun useF n = find (use, n)
      val liveIn = ref (mkDict(cmpNode))
      val liveOut = ref (mkDict(cmpNode))
      val liveIn' = ref (mkDict(cmpNode))
      val liveOut' = ref (mkDict(cmpNode))
      fun compareDict a b =
        let val l = ListPair.zip (listItems a, listItems b)
        in List.foldl (fn (((_,x),(_,y)), b) => b andalso (equal(x,y))) true l
        end
      val listNodes = List.rev (nodes control)
      val _ = List.app (fn n => ( liveIn   := insert(!liveIn, n, empty(String.compare));
                                  liveOut  := insert(!liveOut, n, empty(String.compare));
                                  liveIn'  := insert(!liveIn', n, empty(String.compare));
                                  liveOut' := insert(!liveOut', n, empty(String.compare)))) listNodes
      fun alive n =
            let val _ = liveIn'  := insert(!liveIn', n, find(!liveIn, n))
                val _ = liveOut' := insert(!liveOut', n, find(!liveOut, n))
                val predIn =  let val p = pred n
                              in List.foldl (fn (n, s) => union (s, (find(!liveIn, n)))) (empty(String.compare)) p
                              end
                val _ = liveOut := insert(!liveOut, n, predIn)
                val i = union (useF n, difference (find (!liveOut, n), defF n))
                val _ = liveIn := insert(!liveIn, n, i)
            in ()
            end
      val iter = List.app alive
    in
      (iter listNodes ;
      while ((compareDict (!liveIn) (!liveIn')) andalso (compareDict (!liveOut) (!liveOut')))
        do (iter listNodes);
        fn n => find(!liveOut, n))
    end

    (*fun interferenceGraph fg =
      let
        val liveMap = liveAnalysis fg
        val regs = ()
      in

      end*)

end
