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

  fun alloc (instr, frame) =
    let
      fun preparation () =
        let
          val (fg as FGRAPH{control, def, use, ismove}, listNodes) = makeGraph instr
          val instrnode = ListPair.zip (listNodes, instr)
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
      val frozenMoves = ref emptySNode
      val worklistMoves = ref emptySNode
      val activeMoves = ref emptySNode
      val adjSet = ref (empty(cmpEdg)) (* -> (Temp, Temp)*)
      val adjList = ref (mkDict(String.compare)) (* -> Temp Set*)
      val degree = ref (mkDict(String.compare)) (* -> Int *)
      val moveList = ref (mkDict(String.compare)) (* -> Node Set*)
      val alias = ref (mkDict(String.compare)) (* -> Temp*)
      val color = ref initColor (* -> Temp *)
      val spillCost = ref (mkDict(String.compare))
      val instrs = ref instr

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

      fun build() =
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

      fun freezeMoves u =
        let
          val nm = nodeMoves u
          fun aux n =
            let
              val (x, y) = case nodeToInstr n of
                              (tigerassem.MOVE {src=x, dst=y, ...}) => (x, y)
                              | _ => raise Fail "Shouldn't happen EVA' (freezeMoves)"
              val v = if getAlias y = getAlias u
                      then getAlias x
                      else getAlias y
              val _ = activeMoves := delete (!activeMoves, n)
              val _ = frozenMoves := add(!frozenMoves, n)
              val _ = if isEmpty (nodeMoves v) andalso (find (!degree, v) < K)
                      then (freezeWorkList := delete (!freezeWorkList, v) ;
                            simplifyWorkList := add(!simplifyWorkList, v))
                      else ()
            in () end
        in Splayset.app aux nm end

      fun freeze () =
        let
          val n = hd (Splayset.listItems (!freezeWorkList))
          val _ = freezeWorkList := delete (!freezeWorkList, n)
          val _ = simplifyWorkList := add (!simplifyWorkList, n)
        in freezeMoves n end

      fun selectSpill () =
        if isEmpty (!spillWorkList)
        then ()
        else
          let
            val l = Splayset.listItems (!spillWorkList)
            val lInts = List.map (fn s => valOf (Int.fromString (String.substring (s, 1, String.size s - 1)))) l
            val min = List.foldl (fn (x, m) => if x < m then x else m) (hd lInts) (tl lInts)
            val n = "T" ^ Int.toString min
            (* Otra posible heurística, elegir el que tenga mayor interferencia *)
            val _ = spillWorkList := delete (!spillWorkList, n)
            val _ = simplifyWorkList := add (!simplifyWorkList, n)
          in freezeMoves n end

      fun assignColors () =
        (while (not (null (!selectStack))) do
          (let
            val n = pop selectStack
            val okColors = ref (listToSet tigerframe.allregs)
            val adj = find (!adjList, n)
            val _ = Splayset.app (fn w => if member (union (!coloredNodes, precolored), getAlias w)
                                          then okColors := delete (!okColors, find(!color, getAlias w))
                                          else ()) adj
            val _ = if isEmpty (!okColors)
                    then spilledNodes := add (!spilledNodes, n)
                    else (coloredNodes := add(!coloredNodes, n) ;
                          color := insert(!color, n,  hd (Splayset.listItems (!okColors))))
          in () end);
        Splayset.app (fn n => color := insert(!color, n, find(!color, getAlias n))) (!coalescedNodes))

      fun rewriteProgram () =
        let
          val newTemps  = ref emptySTemp
          val dictFrame = Splayset.foldl (fn (t, d) => case tigerframe.allocLocal frame true of
                                                          tigerframe.InFrame n => insert(d, t, n)
                                                          | _       => raise Fail "Shouldn't happen (rewriteProgram)") (mkDict(String.compare)) (!spilledNodes)
          fun store ts def =
            let
              val n = find(dictFrame, def)
            in
              tigerassem.OPER {assem = "movb `s0, " ^ Int.toString n ^ "(`s1)", src = [ts, tigerframe.fp], dst = [], jump = NONE }
            end

          fun fetch ts use =
            let
              val n = find(dictFrame, use)
            in
              tigerassem.OPER { assem = "movb " ^ Int.toString n ^ "(`s0), `d0", src = [tigerframe.fp], dst = [ts], jump = NONE }
            end

          fun rwDef instr def =
            if member (!spilledNodes, def)
            then let
                   val t = tigertemp.newtemp()
                   val _ = newTemps := add(!newTemps, t)
                   val storeInstr = store t def
                 in case instr of
                      tigerassem.MOVE {assem, src, dst} => let
                                                             val dst' = if dst = def then t else dst
                                                             val instr' = tigerassem.MOVE {assem=assem, src=src, dst=dst'}
                                                           in (instr', SOME storeInstr) end
                    | tigerassem.OPER {assem, src, dst, jump} => let
                                                                    val dst' = List.map (fn x => if x = def then t else x) dst
                                                                    val instr' = tigerassem.OPER {assem=assem, src=src, dst=dst', jump=jump}
                                                                  in (instr', SOME storeInstr) end
                    | _                                         => raise Fail "Shouln't happen (rwDef, LABEL)" (* VER *)
                  end
            else (instr, NONE)

          fun rwUse instr use =
            if member (!spilledNodes, use)
            then let
                   val t = tigertemp.newtemp()
                   val _ = newTemps := add(!newTemps, t)
                   val fetchInstr = fetch t use
                 in case instr of
                     tigerassem.MOVE {assem, src, dst} => let
                                                            val src' = if src = use then t else src
                                                            val instr' = tigerassem.MOVE {assem=assem, src=src', dst=dst}
                                                          in (instr', SOME fetchInstr) end
                   | tigerassem.OPER {assem, src, dst, jump} =>  let
                                                                   val src' = List.map (fn x => if x = use then t else x) src
                                                                   val instr' = tigerassem.OPER {assem=assem, src=src', dst=dst, jump=jump}
                                                                 in (instr', SOME fetchInstr) end
                   | _                                        => raise Fail "Shouln't happen (rwUse, LABEL)" (* VER *)
                end
            else (instr, NONE)

          fun comb f instr l [] = (instr, l)
          | comb f instr l (x::xs) =
              case f instr x of
                (_, NONE) => comb f instr l xs
              | (instr', SOME instrfs) => comb f instr' (instrfs :: l) xs

          fun procInstr pre [] = List.rev pre
          | procInstr pre (instr::ps) =
              case instr of
                tigerassem.MOVE {src, dst, ...} =>
                  let
                    val (instr0, l0) = comb rwUse instr [] [src]
                    val (instr1, l1) = comb rwDef instr0 [] [dst]
                  in procInstr (l1 @ (instr1::l0) @ pre) ps end
                | tigerassem.OPER {src, dst, ...} =>
                  let
                    val (instr0, l0) = comb rwUse instr [] src
                    val (instr1, l1) = comb rwDef instr0 [] dst
                  in procInstr (l1 @ (instr1::l0) @ pre) ps end
                | _ => procInstr (instr :: pre) ps

          val rwInstrs = procInstr [] (!instrs)
          val _ = instrs := rwInstrs
          val _ = initial := union (!coloredNodes, union (!coalescedNodes, !newTemps))
          val _ = spilledNodes := emptySTemp
          val _ = coloredNodes := emptySTemp
          val _ = coalescedNodes := emptySTemp
        in () end

        fun main () =
          let
            val _ = build()
            val _ = makeWorkList()
            fun iter () = ( if not (isEmpty (!simplifyWorkList )) then (simplify(); iter())
                            else if not (isEmpty (!worklistMoves)) then (coalesce(); iter())
                            else if not (isEmpty (!freezeWorkList)) then (freeze(); iter())
                            else if not (isEmpty (!spillWorkList)) then (selectSpill(); iter())
                            else ())
            in
              (iter();
              assignColors();
              if not (isEmpty (!spilledNodes))
              then (rewriteProgram(); main())
              else () )
            end

        val _ = main()
    in
      (!color, !instrs)
    end

end
