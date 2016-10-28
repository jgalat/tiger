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
  val initColor = List.foldl (fn (r, dict) => insert(dict, r, r)) (mkDict(String.compare)) tigerframe.allregs

  fun safeFind (d, k, i) =
    case peek (d, k) of
      SOME s => s
      |NONE  => i

  val emptySTemp = empty (String.compare)
  val emptySNode = empty (tigergraph.cmpNode)

  fun alloc (instrs, frame) =
    let
    fun preparation () =
      let
        val (fg as FGRAPH{control, def, use, ismove}, listNodes) = makeGraph instrs
        val instrnode = ListPair.zip (listNodes, instrs)
        val dictInstrNode = List.foldl (fn ((n, i), d) => insert (d, n, i)) (mkDict (tigergraph.cmpNode)) instrnode
        val (liveMap, _) = tigerliveness.liveAnalysis fg
        val listNodes = nodes (control)
        val tempslm = List.foldl (fn (n, s) => union (s, liveMap n)) (empty(String.compare)) listNodes
        val temps = List.foldl (fn (n, s) => union (s, find(def, n))) tempslm listNodes
        val initial = Splayset.difference (temps, precolored)
      in  (initial, fg, liveMap, fn x => find(dictInstrNode, x))
      end

      val (init, fg as FGRAPH{control, def, use, ismove}, liveMap, nodeToInstr) = preparation()
      fun defF n = find (def, n)
      fun useF n = find (use, n)
      val initial = ref init
      val simplifyWorkList = ref emptySTemp
      val freezeWorkList = ref emptySTemp
      val spillWorkList = ref emptySTemp
      val spilledNodes = ref emptySTemp
      val coalescedNodes = ref emptySTemp
      val coloredNodes = ref emptySTemp
      val selectStack = ref []
      val coalescedMoves = ref emptySNode
      val constrainedMoves = ref emptySNode
      val freezeMoves = ref emptySNode
      val worklistMoves = ref emptySNode
      val activeMoves = ref emptySNode
      val adjSet = ref (empty(cmpEdg)) (* -> (Temp, Temp)*)
      val adjList = ref (mkDict(String.compare)) (* -> Temp Set*)
      val degree = ref (mkDict(String.compare)) (* -> Int *)
      val moveList = ref (mkDict(String.compare)) (* -> Node Set*)
      val alias = ref (mkDict(String.compare)) (* -> Temp*)
      val color = ref initColor
      val spillCost = ref (mkDict(String.compare))

      fun addEdge (t1, t2) =
        (if (not (member(!adjSet, (t1, t2)))) andalso (t1 <> t2)
        then adjSet := addList (!adjSet, [(t1, t2), (t2, t1)])
        else ();
        if (not (member(precolored, t1)))
        then (adjList := insert(!adjList, t1, add(safeFind(!adjList, t1, emptySTemp), t2)) ;
              degree := insert (!degree, t1, safeFind(!degree, t1, 0) + 1))
        else ();
        if (not (member(precolored, t2)))
        then (adjList := insert(!adjList, t2, add(safeFind(!adjList, t2, emptySTemp), t1)) ;
              degree := insert (!degree, t2, safeFind(!degree, t2, 0) + 1))
        else ())

      fun Build() =
        let
          val lRevNodes = List.rev (nodes control)
          val live = ref (emptySTemp)
          fun auxLive iNode =
            let
              val _ = live := liveMap iNode
              val _ = if find(ismove, iNode)
                      then
                        (live := difference (!live, useF iNode);
                        Splayset.app (fn n => moveList := insert(!moveList, n, add(safeFind(!moveList, n, emptySNode), iNode))) (union (defF iNode, useF iNode));
                        worklistMoves := add(!worklistMoves, iNode))
                      else ()
              val _ = live := union (!live, defF iNode)
              val _ = Splayset.app (fn d => Splayset.app (fn l => addEdge (l, d)) (!live)) (defF iNode)
            in () end
        in
          List.app auxLive lRevNodes
        end

      fun nodeMoves n =
        let val m = find(!moveList, n)
        in intersection (m, union (!activeMoves, !worklistMoves))
        end

      fun moveRelated n = isEmpty (nodeMoves n)

      fun makeWorkList () =
        let
          fun aux n =
            let
              val _ = initial := delete (!initial, n)
              val _ = if (find (!degree, n)) >= K
                      then spillWorkList := add(!spillWorkList, n)
                      else if moveRelated n
                          then freezeWorkList := add(!freezeWorkList, n)
                          else simplifyWorkList := add(!simplifyWorkList, n)
            in ()
            end
        in Splayset.app aux (!initial)
        end

      fun adjacent n =
        let val m = find(!adjList, n)
        in difference (m, union (listToSet (!selectStack), !coalescedNodes))
        end

      fun enableMoves nodes =
        let
          fun aux m =
            if member (!activeMoves, m)
            then (activeMoves := delete(!activeMoves, m);
                  worklistMoves := add(!worklistMoves, m))
            else ()
      in Splayset.app (fn n => Splayset.app aux (nodeMoves n)) nodes
      end

      fun decrementDegree n =
        let
          val d = find(!degree, n)
          val _ = degree := insert (!degree, n, d - 1)
          val _ = if d = K
                  then (enableMoves (add (adjacent n, n)) ;
                        spillWorkList := delete(!spillWorkList, n);
                        if moveRelated n
                        then freezeWorkList := add(!freezeWorkList, n)
                        else simplifyWorkList := add(!simplifyWorkList, n))
                  else ()
          in ()
          end

      fun simplify() =
        if isEmpty(!simplifyWorkList)
        then ()
        else
          let
            val n = hd (Splayset.listItems (!simplifyWorkList))
            val _ = simplifyWorkList := delete (!simplifyWorkList, n)
            val _ = push(n, selectStack)
            val _ = Splayset.app decrementDegree (adjacent n)
          in ()
          end

      fun OK(t, r) =
        ( ((find(!degree, t)) < K) orelse (member(precolored, t)) orelse (member (!adjSet, (t,r))))

      fun addWorkList u =
        if (not (member (precolored, u))) andalso (not (moveRelated u)) andalso (find(!degree, u) < K)
        then (freezeWorkList := delete(!freezeWorkList, u);
              simplifyWorkList := delete(!simplifyWorkList, u))
        else ()

      fun conservative nodes =
        let
          val k = Splayset.foldl (fn (n, k) => if (find(!degree, n) >= K)
                                               then k+1
                                               else k) 0 nodes
        in k < K
        end

      fun getAlias n =
        if (member(!coalescedNodes, n))
        then getAlias (find(!alias, n))
        else n

      fun combine (u, v) =
        let
          val _ = if (member (!freezeWorkList, v))
                  then (freezeWorkList := delete(!freezeWorkList, v))
                  else (spillWorkList := delete(!spillWorkList, v))
          val _ = coalescedNodes := add(!coalescedNodes, v)
          val _ = alias := insert(!alias, v, u)
          val _ = moveList := insert(!moveList, u, union (find(!moveList, u), find(!moveList, v)))
          val _ = enableMoves (singleton String.compare v)
          val _ = Splayset.app (fn t => (addEdge(t, u); decrementDegree t)) (adjacent v)
          val _ = if (find(!degree, u) >= K) andalso (member (!freezeWorkList, u))
                  then (freezeWorkList := delete(!freezeWorkList, u);
                        spillWorkList := delete(!spillWorkList, u))
                  else ()
        in ()
        end

    fun coalesce () =
      if isEmpty(!worklistMoves)
      then ()
      else
        let
          val n = hd (Splayset.listItems (!worklistMoves))
          val (x,y) = case nodeToInstr n of
                        (tigerassem.MOVE {src=x, dst=y, ...}) => (x, y)
                      | _ => raise Fail "Shouldn't happen EVA' (coalesce)"
          val x = getAlias x
          val y = getAlias y
          val (u, v) = if member(precolored, y) then (y, x) else (x, y)
          val _ = worklistMoves := delete(!worklistMoves, n)
          val _ = if u = v
                  then (coalescedMoves := add(!coalescedMoves, n);
                       addWorkList u)
                  else if (member(precolored, v)) orelse (member(!adjSet, (u, v)))
                       then (constrainedMoves := add(!constrainedMoves, n);
                            addWorkList u;
                            addWorkList v)
                       else
                        let val b = Splayset.foldl (fn (t,b) => OK (t,u) andalso b) true (adjacent v)
                        in if ((member(precolored, u) andalso b) orelse
                                ((not(member(precolored, u))) andalso (conservative (union (adjacent v, adjacent u)))))
                           then (coalescedMoves := add(!coalescedMoves, n);
                                combine(u, v);
                                addWorkList u)
                           else activeMoves := add(!activeMoves, n)
                        end
          in () end


    in
      ()
    end

end
