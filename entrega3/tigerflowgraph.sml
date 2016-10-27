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

    fun printNodos ls = List.app (fn (a,n) => print((nodename n)^" => \n")) ls

    fun printLabels labs = List.app (fn (l,n)=>print(l^" => "^(nodename n)^"\n")) (tabAList labs)

    fun printDatosNodo (n:node) (d:tigertemp.temp set nodeDict) (u:tigertemp.temp set nodeDict) m =
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

    fun printFlowGraph g d u m = List.app (fn n => printDatosNodo n d u m) (nodes g)

    fun makeGraph instrList =
      let val g = newGraph()
          val tl = ref (tigertab.tabNueva())
          fun inl [] = []
          |   inl ((lab as LABEL {lab = l, ...}) :: t) =
                let val n = newNode g
                    (*val _ = print ("-INSERTADA - $$"^l^"$$\n")*)
                in tl := tigertab.tabInserta(l, n, !tl);
                   (lab, n) :: inl t
                end
          |   inl (x :: t) = (x , newNode g) :: inl t
          val nl = inl instrList

          (*val _ = (print "IMPRIMIR TABLA\n" ; List.app (fn (l, n) =>  print ("label " ^ l ^"\n")) (tabAList (!tl)))*)
          fun listToSet l = addList (empty String.compare, l)
          fun instrNode [] x = x
            | instrNode [(OPER {src = src, dst = dst, jump = NONE, ...}, node)] (d, u, im) =
               let
                  val newD = insert(d, node, listToSet dst)
                  val newU = insert(u, node, listToSet src)
                  val newIm = insert(im, node, false)
               in
                 (newD, newU, newIm)
              end
           | instrNode ((OPER {src = src, dst = dst, jump = NONE, ...}, node)::(i,node2)::t) (d, u, im) =
              let
                 val newD = insert(d, node, listToSet dst)
                 val newU = insert(u, node, listToSet src)
                 val newIm = insert(im, node, false)
                 val _ = mk_edge {from = node, to = node2}
              in
                instrNode ((i,node2)::t) (newD, newU, newIm)
             end
           | instrNode ((OPER {src = src, dst = dst, jump = SOME ls, ...}, node)::t) (d, u, im) =
              let
                 val newD = insert(d, node, listToSet dst)
                 val newU = insert(u, node, listToSet src)
                 val newIm = insert(im, node, false)
                 val _ = List.app (fn l => mk_edge {from = node, to = tabSaca (l, !tl)}) ls
              in
                instrNode t (newD, newU, newIm)
             end
           | instrNode [(MOVE {src = src, dst = dst, ...}, node)] (d, u, im) =
              let
                 val newD = insert(d, node, singleton String.compare dst)
                 val newU = insert(u, node, singleton String.compare src)
                 val newIm = insert(im, node, true)
              in
                (newD, newU, newIm)
             end
           | instrNode ((MOVE {src = src, dst = dst,  ...}, node)::(i,node2)::t) (d, u, im) =
              let
                 val newD = insert(d, node, singleton String.compare dst)
                 val newU = insert(u, node, singleton String.compare src)
                 val newIm = insert(im, node, true)
                 val _ = mk_edge {from = node, to = node2}
              in
                instrNode ((i,node2)::t) (newD, newU, newIm)
             end
           | instrNode [(LABEL _, node)] (d, u, im) =
              let
                val newD = insert(d, node, empty(String.compare))
                val newU = insert(u, node, empty(String.compare))
                val newIm = insert(im, node, false)
              in
                (newD, newU, newIm)
              end
           | instrNode ((LABEL _, node)::(i,node2)::t) (d, u, im) =
              let
                val newD = insert(d, node, empty(String.compare))
                val newU = insert(u, node, empty(String.compare))
                val newIm = insert(im, node, false)
                val _ = mk_edge {from = node, to = node2}
              in
                instrNode ((i,node2)::t) (newD, newU, newIm)
             end
          val (d, u, im) = instrNode nl (mkDict(cmpNode), mkDict(cmpNode), mkDict(cmpNode))
          (*val _ = printFlowGraph g d u im*)
      in (FGRAPH {control = g, def = d, use = u, ismove = im }, List.map #2 nl)
      end
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
