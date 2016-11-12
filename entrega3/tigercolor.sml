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

  fun safeFind(d, k, i) =
    case peek (d, k) of
      SOME s => s
      |NONE  => i

  fun safeDelete (s, i) =
    if (member (s, i))
    then (delete (s,i))
    else s

  val emptySTemp = empty (String.compare)
  val emptySNode = empty (tigergraph.cmpNode)

  fun alloc' (instr, frame, init) =
    let
      fun preparation () =
        let
          val (fg as FGRAPH{control, def, use, ismove}, listNodes) = makeGraph instr
          val instrnode = ListPair.zip (listNodes, instr)
          val dictInstrNode = List.foldl (fn ((n, i), d) => insert (d, n, i)) (mkDict (tigergraph.cmpNode)) instrnode
          val (liveMap, _) = tigerliveness.liveAnalysis fg
        in  (fg, liveMap, fn x => find(dictInstrNode, x) handle NotFound => raise Fail "preparation1")
        end

      val (fg as FGRAPH{control, def, use, ismove}, liveMap, nodeToInstr) = preparation()
      fun defF n = find(def, n) handle NotFound => raise Fail "DEFF"
      fun useF n = find(use, n) handle NotFound => raise Fail "USEF"
      val initial = ref init
      (*val _ = (Splayset.app (fn x => print(x^", ")) init; print("\n"))*)
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
        if (not (member(!adjSet, (t1, t2)))) andalso (t1 <> t2)
        then  (adjSet := addList (!adjSet, [(t1, t2), (t2, t1)]);
              if (not (member(precolored, t1)))
              then (adjList := insert(!adjList, t1, add(safeFind(!adjList, t1, emptySTemp), t2)) ;
                    degree := insert (!degree, t1, safeFind(!degree, t1, 0) + 1))
              else ();
              if (not (member(precolored, t2)))
              then (adjList := insert(!adjList, t2, add(safeFind(!adjList, t2, emptySTemp), t1)) ;
                    degree := insert (!degree, t2, safeFind(!degree, t2, 0) + 1))
              else ())
        else ()

      fun printAdjSet() =
        let val _ = print ("strict graph " ^ tigerframe.name frame ^ " {")
            fun dq s = "\"" ^ s ^ "\""
            val _ = Splayset.app (fn (x, y) => (print (dq x); print " -- "; print (dq y); print "; ")) (!adjSet)
            val _ = print "}\n"
        in () end

      fun build() =
        let
          val lRevNodes = List.rev (nodes control)
          val live = ref (emptySTemp)
          fun auxLive iNode =
            let
              val _ = live := liveMap iNode
              val _ = if find(ismove, iNode) handle NotFound => raise Fail "AUXLIVE BUILD"
                      then
                        (live := difference (!live, useF iNode);
                        Splayset.app (fn n => moveList := insert(!moveList, n, add(safeFind(!moveList, n, emptySNode), iNode))) (union (defF iNode, useF iNode));
                        worklistMoves := add(!worklistMoves, iNode))
                      else ()
              val _ = live := union (!live, defF iNode)
              val _ = Splayset.app (fn d => Splayset.app (fn l => addEdge (l, d)) (!live)) (defF iNode)
            in () end
        in
          (*(List.app auxLive lRevNodes; printAdjSet())*)
          List.app auxLive lRevNodes
        end

      fun nodeMoves n =
        let val m = safeFind(!moveList, n, emptySNode)
        in intersection (m, union (!activeMoves, !worklistMoves))
        end

      fun moveRelated n = not(isEmpty (nodeMoves n))

      fun makeWorkList () =
        let
          fun aux n =
            let
              val _ = initial := safeDelete(!initial, n)
              val _ = if (safeFind(!degree, n, 0) >= K)
                      then spillWorkList := add(!spillWorkList, n)
                      else if moveRelated n
                          then freezeWorkList := add(!freezeWorkList, n)
                          else simplifyWorkList := add(!simplifyWorkList, n)
            in ()
            end
        in Splayset.app aux (!initial)
        end

      fun adjacent n =
        let val m = safeFind(!adjList, n, emptySTemp)
        in difference (m, union (listToSet (!selectStack), !coalescedNodes))
        end

      fun enableMoves nodes =
        let
          fun aux m =
            if member (!activeMoves, m)
            then (activeMoves := safeDelete(!activeMoves, m);
                  worklistMoves := add(!worklistMoves, m))
            else ()
      in Splayset.app (fn n => Splayset.app aux (nodeMoves n)) nodes
      end

      fun decrementDegree n =
        let
          val d = safeFind(!degree, n, 0)
          val _ = degree := insert (!degree, n, Int.max(d - 1, 0))
          val _ = if d = K
                  then (enableMoves (add (adjacent n, n));
                        spillWorkList := safeDelete(!spillWorkList, n);
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
            val _ = simplifyWorkList := safeDelete(!simplifyWorkList, n)
            (*val _ = print ("--------------------" ^ n ^ "---------------------\n")*)
            val _ = push n selectStack
            val _ = Splayset.app decrementDegree (adjacent n)
          in ()
          end

      fun OK(t, r) =
        ( ( (safeFind(!degree, t, 0)) < K) orelse (member(precolored, t)) orelse (member (!adjSet, (t,r))))

      fun addWorkList u =
        if (not (member (precolored, u))) andalso (not (moveRelated u)) andalso ((safeFind(!degree, u, 0) < K))
        then (freezeWorkList := safeDelete(!freezeWorkList, u);
              simplifyWorkList := add(!simplifyWorkList, u))
        else ()

      fun conservative nodes =
        let
          val k = Splayset.foldl (fn (n, k) => if (safeFind(!degree, n, 0) >= K)
                                               then k + 1
                                               else k) 0 nodes
        in k < K
        end

      fun getAlias n =
        if (member(!coalescedNodes, n))
        then getAlias (find(!alias, n) handle NotFound => raise Fail "GETALIAS")
        else n

      fun combine (u, v) =
        let
          (*val _ = print ("combined " ^ u ^ " " ^ v ^ "\n")*)
          val _ = if (member (!freezeWorkList, v))
                  then freezeWorkList := safeDelete(!freezeWorkList, v)
                  else spillWorkList := safeDelete(!spillWorkList, v)
          val _ = coalescedNodes := add(!coalescedNodes, v)
          val _ = alias := insert(!alias, v, u)
          val _ = moveList := insert(!moveList, u, union (safeFind(!moveList, u, emptySNode), safeFind(!moveList, v, emptySNode)))
          val _ = enableMoves (singleton String.compare v)
          val _ = Splayset.app (fn t => (addEdge(t, u); decrementDegree t)) (adjacent v)
          val _ = if (safeFind(!degree, u, 0) >= K) andalso (member (!freezeWorkList, u))
                  then (freezeWorkList := safeDelete(!freezeWorkList, u);
                        spillWorkList := add(!spillWorkList, u))
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
                        | _ => raise Fail "Shouldn't happen (coalesce)"
            val x = ((*print ("getAlias " ^ x ^ " == " ^ getAlias x ^ "\n") ;*) getAlias x)
            val y = ((*print ("getAlias " ^ y ^ " == " ^ getAlias y ^ "\n") ;*) getAlias y)
            val (u, v) = if member(precolored, y) then (y, x) else (x, y)
            val _ = worklistMoves := safeDelete(!worklistMoves, n)
            val _ = if u = v
                    then (coalescedMoves := add(!coalescedMoves, n);
                         addWorkList u)
                    else if (member(precolored, v)) orelse (member(!adjSet, (u, v)))
                         then (constrainedMoves := add(!constrainedMoves, n);
                              addWorkList u;
                              addWorkList v)
                         else
                          let val b =  Splayset.foldl (fn (t, b) => OK (t,u) andalso b) true (adjacent v)
                          in if ((member(precolored, u) andalso b) orelse
                                  ((not(member(precolored, u))) andalso (conservative (union (adjacent u, adjacent v)))))
                             then (coalescedMoves := add(!coalescedMoves, n);
                                  combine(u, v);
                                  addWorkList u)
                             else (activeMoves := add(!activeMoves, n))
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
              val _ = activeMoves := safeDelete(!activeMoves, n)
              val _ = frozenMoves := add(!frozenMoves, n)
              val _ = if isEmpty (nodeMoves v) andalso (safeFind(!degree, v, 0) < K)
                      then (freezeWorkList := safeDelete(!freezeWorkList, v);
                            simplifyWorkList := add(!simplifyWorkList, v))
                      else ()
            in () end
        in Splayset.app aux nm end

      fun freeze () =
        let
          val u = hd (Splayset.listItems (!freezeWorkList))
          val _ = freezeWorkList := safeDelete(!freezeWorkList, u)
          val _ = simplifyWorkList := add (!simplifyWorkList, u)
        in freezeMoves u end

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
            val _ = spillWorkList := safeDelete(!spillWorkList, n)
            val _ = simplifyWorkList := add (!simplifyWorkList, n)
          in freezeMoves n end

      fun assignColors () =
        (while (not (null (!selectStack))) do
          (let
            val n = pop selectStack
            (*val _ = print ("****************" ^ n ^ "****************\n")*)
            val okColors = ref (listToSet tigerframe.allregs)
            val adj = safeFind(!adjList, n, emptySTemp)
            val _ = Splayset.app (fn w => if member (union (!coloredNodes, precolored), getAlias w)
                                          then ((*print ("NODO " ^ w ^ " " ^ (getAlias w) ^ "\n") ;*)
                                                okColors := safeDelete(!okColors, find(!color, getAlias w))) (* Quité safeFind *)
                                          else ()) adj
            val _ = if isEmpty (!okColors)
                    then spilledNodes := add (!spilledNodes, n)
                    else (coloredNodes := add(!coloredNodes, n);
                          color := insert(!color, n,  hd (Splayset.listItems (!okColors)))
                          (*print ("colored " ^ n ^ " with " ^ hd (Splayset.listItems (!okColors)) ^ "\n")*)
                          )
          in () end);
        Splayset.app (fn n => color := insert(!color, n, safeFind(!color, getAlias n, ""))) (!coalescedNodes))

      fun rewriteProgram () =
        let
          val newTemps  = ref emptySTemp
          val dictFrame = Splayset.foldl (fn (t, d) => case tigerframe.allocLocal frame true of
                                                          tigerframe.InFrame n => insert(d, t, n)
                                                          | _       => raise Fail "Shouldn't happen (rewriteProgram)") (mkDict(String.compare)) (!spilledNodes)
          fun store ts def =
            let
              val n = find(dictFrame, def) handle NotFound => raise Fail "STORE RW"
            in
              tigerassem.OPER {assem = "movl `s0, " ^ Int.toString n ^ "(`s1)", src = [ts, tigerframe.fp], dst = [], jump = NONE }
            end

          fun fetch ts use =
            let
              val n = find(dictFrame, use) handle NotFound => raise Fail "FETCH RW"
            in
              tigerassem.OPER { assem = "movl " ^ Int.toString n ^ "(`s0), `d0", src = [tigerframe.fp], dst = [ts], jump = NONE }
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
          (*val _ = spilledNodes := emptySTemp
          val _ = coloredNodes := emptySTemp
          val _ = coalescedNodes := emptySTemp*)
        in () end

        fun main () =
          let
            val _ = build()
            val _ = makeWorkList()
            fun iter () = ( if not (isEmpty (!simplifyWorkList )) then (simplify(); iter())
                            else if not (isEmpty (!worklistMoves)) then (coalesce(); iter())
                            else if not (isEmpty (!spillWorkList)) then (selectSpill(); iter())
                            else if not (isEmpty (!freezeWorkList)) then (freeze(); iter())
                            else ())
            in
              (iter();
              assignColors();
              if not (isEmpty (!spilledNodes))
              then (
                    (*print ("rewriteProgram- " ^ (Int.toString (Splayset.numItems(!spilledNodes))) ^ " --\n");*)
                    (*Splayset.app (fn x => (print x; print ", ")) (!spilledNodes); print "\n";*)
                    rewriteProgram();
                    alloc' (!instrs, frame, !initial))
              else (!color, !instrs))
            end
    in
      main()
    end

fun alloc(instr, frame) =
 let
   fun deleteMoves color [] instr = rev instr
   | deleteMoves color ((ins as tigerassem.MOVE{src, dst, ...}) :: inss) instr =
     if (find(color, src) = find(color, dst))
     then deleteMoves color inss instr
     else deleteMoves color inss (ins :: instr)
   | deleteMoves color (ins :: inss) instr = deleteMoves color inss (ins :: instr)

   fun getRegs (tigerassem.MOVE {src=src, dst=dst, ...}, s) = addList (s,[src, dst])
            | getRegs (tigerassem.OPER {src=src, dst=dst, ...}, s) = addList (s, src @ dst)
            | getRegs (_, s) = s

   val allTemps = List.foldl getRegs emptySTemp instr
   val init = difference(allTemps, precolored)

   val (color, instrs) = alloc' (instr, frame, init)
   val cleansedInstrs = deleteMoves color instrs []
 in
    (color, instrs)
 end

end
