structure tigercolor :> tigercolor =
struct

  open Splayset
  open Splaymap
  open tigerflowgraph
  open tigergraph

  type allocation = (tigertemp.temp, tigerframe.register) Splaymap.dict
  
  fun listToSet l = addList (empty String.compare, l)

  val precolored = listToSet (tigerframe.allregs)
  val K = Splayset.numItems precolored

  fun push x s = s := (x :: !s)
  fun pop s = (hd (!s)) before (s := tl (!s))
  val null = List.null

  fun cmpEdg ((a, b), (c, d)) = case String.compare (a, c) of
                                  EQUAL => String.compare (b, d)
                                | x => x
  fun initColor () = ()

  fun alloc (instrs, frame) =
    let
    fun preparation () =
      let
        val (fg as FGRAPH{control, def, use, ismove}, listNodes) = makeGraph instrs
        val instrnode = ListPair.zip (listNodes, instrs)
        val dictInstrNode = List.foldl (fn ((n, i), d) => insert (d, n, i)) (mkDict (tigergraph.cmpNode)) instrnode
        val (liveMap, _) = tigerliveness.liveAnalysis fg
        val listNodes = tigergraph.nodes (control)
        val tempslm = List.foldl (fn (n, s) => union (s, liveMap n)) (empty(String.compare)) listNodes
        val temps = List.foldl (fn (n, s) => union (s, find(def, n))) tempslm listNodes
        val initial = Splayset.difference (temps, precolored)
      in  (initial, fg, liveMap, fn x => find(dictInstrNode, x))
      end

      val (initial, flow, liveMap, nodeToInstr) = preparation()
      val simplifyWorkList = ref (empty (String.compare))
      val freezeWorkList = ref (empty (String.compare))
      val spillWorkList = ref (empty (String.compare))
      val spilledNodes = ref (empty (String.compare))
      val coalescedNodes = ref (empty (String.compare))
      val coloredNodes = ref (empty (String.compare))
      val selectStack = ref []
      val coalescedMoves = ref (empty (tigergraph.cmpNode))
      val constrainedMoves = ref (empty (tigergraph.cmpNode))
      val freezeMoves = ref (empty (tigergraph.cmpNode))
      val worklistMoves = ref (empty (tigergraph.cmpNode))
      val activeMoves = ref (empty (tigergraph.cmpNode))
      val adjSet = ref (empty(cmpEdg))
      val adjList = ref (mkDict(String.compare))
      val degree = ref (mkDict(String.compare))
      val moveList = ref (mkDict(String.compare))
      val alias = ref (mkDict(String.compare))
      val color = ref (initColor())


    in
    ()
    end

end
