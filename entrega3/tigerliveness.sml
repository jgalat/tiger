structure tigerliveness :> tigerliveness =
struct

  open Splayset
  open Splaymap
  open tigergraph
  open tigerflowgraph

  fun printFGNodo (n:node) (d:tigertemp.temp set nodeDict) u m =
                          (print("Nodo: "^nodename n^"\n  Pred: ");
                           List.app (fn n => print(nodename n^" ")) (pred n);
                           print("\n  Succ: ");
                           List.app (fn n => print(nodename n^" ")) (succ n);
                           if isSome(peek(d,n)) then (
                               print("\n  Def: ");
                               List.app (fn l => print(l^" ")) (Splayset.listItems (find(d,n)));
                               print("\n  Use: ");
                               List.app (fn l => print(l^" ")) (Splayset.listItems (find(u,n)));
                               print("\n  Move: ");
                               print(if find(m,n) then "True" else "False")) else ();
                           print("\n"))

  fun liveAnalysis (FGRAPH {control, def, use, ismove}) =
    let
      fun defF n = find (def, n)
      fun useF n = find (use, n)
      fun f m = Splaymap.app (fn (k, a) => (print "TEMPS: "; Splayset.app (fn x => print ("-"^x^"")) a; print "\n")) m
      val liveIn = ref (mkDict(cmpNode))
      val liveOut = ref (mkDict(cmpNode))
      val liveIn' = ref (mkDict(cmpNode))
      val liveOut' = ref (mkDict(cmpNode))
      fun compareDict a b =
        let val l = ListPair.zip (listItems a, listItems b)
        in List.foldl (fn (((_,x),(_,y)), b) => b andalso (Splayset.equal(x,y))) true l
        end
      val listNodes = nodes control
      val _ = List.app (fn n => ( liveIn   := insert(!liveIn, n, empty(String.compare));
                                  liveOut  := insert(!liveOut, n, empty(String.compare));
                                  liveIn'  := insert(!liveIn', n, empty(String.compare));
                                  liveOut' := insert(!liveOut', n, empty(String.compare)))) listNodes
      fun alive n =
            let
                (*val _ = printFGNodo n def use ismove*)
                val _ = liveIn'  := insert(!liveIn', n, find(!liveIn, n))
                val _ = liveOut' := insert(!liveOut', n, find(!liveOut, n))
                val i = union (useF n, difference (find (!liveOut, n), defF n))
                val _ = liveIn := insert(!liveIn, n, i)
                val predIn =  let val p = succ n
                              in List.foldl (fn (n, s) => union (s, (find(!liveIn, n)))) (empty(String.compare)) p
                              end
                val _ = liveOut := insert(!liveOut, n, predIn)
            in ()
            end
      val iter = List.app alive
    in
      (
      iter listNodes ;
      while (not ((compareDict (!liveIn) (!liveIn')) andalso (compareDict (!liveOut) (!liveOut'))))
        do (iter listNodes);
        let val dict = transform (Splayset.listItems) (!liveOut)
        in (fn n => find(!liveOut, n) handle NotFound => raise Fail "LIVEMAP",
            fn n => find(dict, n) handle NotFound => raise Fail "LIVEMAP 2")
        end)
    end

    datatype igraph = IGRAPH of {graph : tigergraph.graph,
                                tnode : tigertemp.temp -> tigergraph.node,
                                gtemp : tigergraph.node -> tigertemp.temp,
                                moves : (tigergraph.node * tigergraph.node) list}

    fun interferenceGraph (fg as (FGRAPH {control, def, use, ismove}))  =
      let
        val (liveMap, liveMapList) = liveAnalysis fg
        val listNodes = nodes control
        val graph = newGraph()
        val tempslm = List.foldl (fn (n, s) => union (s, liveMap n)) (empty(String.compare)) listNodes
        val temps = List.foldl (fn (n, s) => union (s, find(def, n))) tempslm listNodes

        fun printNode s n = print (s ^ ": " ^(nodename n)^"\n")
        val tNodes = List.map (fn x => (x, newNode graph)) (Splayset.listItems temps)
        val mapTNode = List.foldl (fn ((x, n),t) => insert (t, x, n)) (mkDict(String.compare)) tNodes
        fun tnode t  = find(mapTNode, t)
        val mapGTemp = List.foldl (fn ((x, n), t) => insert(t, n, x)) (mkDict(cmpNode)) tNodes
        fun gtemp n = find(mapGTemp, n)
        fun printClavesNode m = Splaymap.app (fn (k, _) => print ((nodename k) ^"-")) m
        fun printClavesTemp m = Splaymap.app (fn (k, _) => print (k^"-")) m
        fun defF n = find (def, n)
        fun useF n = find (use, n)
        fun isMoveF n = find (ismove, n)
        fun knit [] moves = moves
        | knit (node::ns) moves =
          if (isMoveF node)
          then (let val source = (case Splayset.listItems (useF node) of
                                    [] => raise Fail "Shouldn't happen (interferenceGraph:knit)"
                                  | (source::_) => source)
                    val dest = (case Splayset.listItems (defF node) of
                                    [] => raise Fail "Shouldn't happen (interferenceGraph:knit)"
                                  | (dest::_) => dest)
                    val loNode = liveMap node
                    val loNodesFiltered = if (member (loNode, source))
                                          then Splayset.delete (loNode, source)
                                          else loNode
                    val newMoves = Splayset.foldl (fn (tlo, m) => (let val (from, to) = (tnode dest, tnode tlo)
                                                                       val _ = if eq (from, to)
                                                                                then ()
                                                                                else mk_edge {from = from, to = to}
                                                                       val nm = if eq (from, to)
                                                                                then m
                                                                                else (from, to) :: m
                                                                   in nm
                                                                   end)) moves loNodesFiltered
                in knit ns newMoves
                end)
          else (let val defNode = defF node
                    val loNode = liveMap node
                in (Splayset.app (fn tdef => Splayset.app (fn tlo => let val (from, to) = (tnode tdef, tnode tlo)
                                                                     in if eq (from, to)
                                                                        then ()
                                                                        else mk_edge {from = tnode tdef, to = tnode tlo}
                                                                     end) loNode) defNode; knit ns moves)
                end)
        val moves = knit listNodes []
      in
        (IGRAPH {graph = graph, tnode = tnode , gtemp = gtemp, moves = moves}, liveMapList)
      end

    fun show (IGRAPH {graph,tnode,gtemp,moves}) =
        (List.app (fn n => (print(gtemp n^": ");
                            Splayset.app (fn t => print(gtemp t^" ")) (addList(empty cmpNode, (adj n)));
                            print("\n"))) (nodes graph);
         print("Moves: ");List.app (fn (t1,t2) => print("("^gtemp t1^","^gtemp t2^") ")) moves;
         print("\n"))

     fun showDot (IGRAPH {graph, tnode, gtemp, moves}) name =
       (print ("strict graph " ^ name ^ " {");
       List.app (fn n => (Splayset.app (fn t => print("\"" ^ gtemp n ^ "\" -- \"" ^ gtemp t ^"\"; ")) (addList(empty cmpNode, (adj n)));
                           print("\n"))) (nodes graph);
        print "}\n")

end
