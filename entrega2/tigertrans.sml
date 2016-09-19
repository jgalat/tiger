structure tigertrans :> tigertrans = struct

open tigerframe
open tigertree
open tigertemp
open tigerabs

exception breakexc
exception divCero

type level = {parent:frame option , frame: frame, level: int}
type access = tigerframe.access

type frag = tigerframe.frag
val fraglist = ref ([]: frag list)

val actualLevel = ref ~1 (* _tigermain debe tener level = 0. *)
fun getActualLev() = !actualLevel

val outermost: level = {parent=NONE,
  frame=newFrame{name="_tigermain", formals=[]}, level=getActualLev()}
fun newLevel{parent={parent, frame, level}, name, formals} =
  {
  parent=SOME frame,
  frame=newFrame{name=name, formals=formals},
  level=level+1}
fun allocArg{parent, frame, level} b = tigerframe.allocArg frame b
fun allocLocal{parent, frame, level} b = tigerframe.allocLocal frame b
fun formals{parent, frame, level} = tigerframe.formals frame

datatype exp =
  Ex of tigertree.exp
  | Nx of tigertree.stm
  | Cx of label * label -> tigertree.stm

fun seq [] = EXP (CONST 0)
  | seq [s] = s
  | seq (x::xs) = SEQ (x, seq xs)

fun unEx (Ex e) = e
  | unEx (Nx s) = ESEQ(s, CONST 0)
  | unEx (Cx cf) =
  let
    val r = newtemp()
    val t = newlabel()
    val f = newlabel()
  in
    ESEQ(seq [MOVE(TEMP r, CONST 1),
      cf (t, f),
      LABEL f,
      MOVE(TEMP r, CONST 0),
      LABEL t],
      TEMP r)
  end

fun unNx (Ex e) = EXP e
  | unNx (Nx s) = s
  | unNx (Cx cf) =
  let
    val t = newlabel()
    val f = newlabel()
  in
    seq [cf(t,f),
      LABEL t,
      LABEL f]
  end

fun unCx (Nx s) = raise Fail ("Error (UnCx(Nx..))")
  | unCx (Cx cf) = cf
  | unCx (Ex (CONST 0)) =
  (fn (t,f) => JUMP(NAME f, [f]))
  | unCx (Ex (CONST _)) =
  (fn (t,f) => JUMP(NAME t, [t]))
  | unCx (Ex e) =
  (fn (t,f) => CJUMP(NE, e, CONST 0, t, f))

fun Ir(e) =
  let  fun aux(Ex e) = tigerit.tree(EXP e)
    | aux(Nx s) = tigerit.tree(s)
    | aux _ = raise Fail "ok, must complete!"
    fun aux2(PROC{body, frame}) = aux(Nx body)
    | aux2(STRING(l, "")) = l^":\n"
    | aux2(STRING("", s)) = "\t"^s^"\n"
    | aux2(STRING(l, s)) = l^":\t"^s^"\n"
    fun aux3 [] = ""
    | aux3(h::t) = (aux2 h)^(aux3 t)
  in  aux3 e end
fun nombreFrame frame = print(".globl " ^ tigerframe.name frame ^ "\n")

(* While y for necesitan la u'ltima etiqueta para un break *)
local
  val salidas: label option tigerpila.Pila = tigerpila.nuevaPila1 NONE
in
  val pushSalida  = tigerpila.pushPila salidas
  fun popSalida() = tigerpila.popPila salidas
  fun topSalida() =
    case tigerpila.topPila salidas of
      SOME l => l
    | NONE => raise Fail "break outside a loop"
end

val datosGlobs = ref ([]: frag list)
fun procEntryExit{level: level, body} =
  let  val label = STRING(name(#frame level), "")
    val body' = PROC{frame= #frame level, body=unNx body}
    val final = STRING(";;-------", "")
  in  datosGlobs:=(!datosGlobs@[label, body', final])
  end

fun getResult() = !datosGlobs

fun stringLen s =
  let  fun aux[] = 0
    | aux(#"\\":: #"x"::_::_::t) = 1+aux(t)
    | aux(_::t) = 1+aux(t)
  in  aux(explode s) end

fun stringExp(s: string) =
  let  val l = newlabel()
    val len = ".long "^makestring(stringLen s)
    val str = ".string \""^s^"\""
    val _ = datosGlobs:=(!datosGlobs @ [STRING(l, len), STRING("", str)])
  in  Ex(NAME l) end

fun preFunctionDec() =
  (pushSalida(NONE);
  actualLevel := !actualLevel+1)

fun functionDec(e, l, proc) =
  let  val body =
        if proc then unNx e
        else MOVE(TEMP rv, unEx e)
    val body' = procEntryExit1(#frame l, body)
    val () = procEntryExit{body=Nx body', level=l}
  in  Ex(CONST 0) end

fun postFunctionDec() =
  (popSalida(); actualLevel := !actualLevel-1)

fun unitExp() = Ex (CONST 0)

fun nilExp() = Ex (CONST 0)

fun intExp(i) = Ex (CONST i)

fun simpleVar(acc, lvl) =
  case acc of
    InReg r => Ex (TEMP r)
  | InFrame k => let fun aux 0 = TEMP fp
                      |  aux n = MEM (BINOP (PLUS, CONST fpPrevLev, aux (n-1)))
                     val aLvl = getActualLev()
                 in Ex (MEM (BINOP (PLUS, aux (aLvl - lvl), CONST k)))
                 end

fun varDec(acc) = simpleVar(acc, getActualLev())

fun fieldVar(var, field) =
  let val varExp = unEx var
      val r = newtemp()
      val fieldAddr = MEM (BINOP (PLUS, TEMP r, CONST (wSz * field)))
  in
    Ex (ESEQ (seq[MOVE (TEMP r, varExp),
                  EXP(externalCall("_checkNil", [TEMP r]))], fieldAddr))
  end

fun subscriptVar(arr, ind) =
let
  val a = unEx arr
  val i = unEx ind
  val ra = newtemp()
  val ri = newtemp()
in
  Ex( ESEQ(seq[MOVE(TEMP ra, a),
    MOVE(TEMP ri, i),
    EXP(externalCall("_checkindex", [TEMP ra, TEMP ri]))],
    MEM(BINOP(PLUS, TEMP ra,
      BINOP(MUL, TEMP ri, CONST tigerframe.wSz)))))
end

fun recordExp(l) =
  let val r = newtemp()
      fun getTemps 0 = []
        | getTemps n = newtemp() :: getTemps (n-1)
			val lenFlds = List.length l
      val regs = getTemps lenFlds
			fun moveFlds ((e,n),t) = (MOVE (TEMP t, unEx e), n, TEMP t)
			val lExReg = map moveFlds (ListPair.zip(l,regs)) (* nice meme *)
			val lExReg' = map #1 lExReg
			(* possible TODO, in case of unordered fields we need to order the fields *)
	in
		Ex (ESEQ (seq (lExReg' @ [EXP (externalCall ("_allocRecord", CONST (lenFlds) :: (List.map #3 lExReg) )),
															MOVE (TEMP r, TEMP rv)]), TEMP r))
	end
fun arrayExp{size, init} =
let
  val s = unEx size
  val i = unEx init
in
  Ex (externalCall("allocArray", [s, i]))
end

fun callExp (name,external,isproc,lev:level,ls) =
  let val actualLev = getActualLev()
      fun menAMay 0 = TEMP fp
        | menAMay n = MEM (BINOP (PLUS, menAMay (n-1), CONST fpPrevLev))
      val fpLev = if (#level lev) = actualLev
                    then MEM (BINOP (PLUS, TEMP fp, CONST fpPrevLev))
                    else if (#level lev) < actualLev
                          then menAMay (actualLev - (#level lev) + 1)
                          else TEMP fp
      fun preparaArgs [] (rt,re) = (rt,re)
         | preparaArgs (h::t) (rt,re) =
            case h of
              Ex (CONST s) => preparaArgs t ((CONST s)::rt, re)
            | Ex (NAME s) => preparaArgs t ((NAME s)::rt, re)
            | Ex (TEMP s) => preparaArgs t ((TEMP s)::rt, re)
            | _           =>  let val t' = newtemp()
                              in preparaArgs t ((TEMP t')::rt, (MOVE (TEMP t', unEx h))::re) end
      val (ta, ls') = preparaArgs (List.rev ls) ([], [])
      val ta' = if external then ta else (fpLev::ta)
    in if isproc then Nx (seq (ls'@[EXP (CALL (NAME name, ta'))]))
       else let val tmp = newtemp()
            in Ex (ESEQ (seq (ls'@[EXP (CALL (NAME name, ta')),
                                  MOVE (TEMP tmp, TEMP rv)]), TEMP tmp))
            end
    end

fun letExp ([], body) = Ex (unEx body)
 |  letExp (inits, body) = Ex (ESEQ(seq inits,unEx body))

fun breakExp() =
  let val ts = topSalida()
  in Nx (JUMP (NAME ts, [ts]))
  end

fun seqExp ([]:exp list) = Nx (EXP(CONST 0))
  | seqExp (exps:exp list) =
    let
      fun unx []   = []
         | unx [e] = []
        | unx (s::ss) = (unNx s)::(unx ss)
    in
      case List.last exps of
        Nx s =>
          let val unexps = map unNx exps
          in Nx (seq unexps) end
        | Ex e => Ex (ESEQ(seq(unx exps), e))
        | cond => Ex (ESEQ(seq(unx exps), unEx cond))
    end

fun preWhileForExp() = pushSalida(SOME(newlabel()))

fun postWhileForExp() = (popSalida(); ())

fun whileExp {test: exp, body: exp, lev:level} =
let
  val cf = unCx test
  val expb = unNx body
  val (l1, l2, l3) = (newlabel(), newlabel(), topSalida())
in
  Nx (seq[LABEL l1,
    cf(l2,l3),
    LABEL l2,
    expb,
    JUMP(NAME l1, [l1]),
    LABEL l3])
end

fun forExp {lo, hi, var, body} =
  let val var' = unEx var
      val (l1, l2, lsal) = (newlabel(), newlabel(), topSalida())
  in
     Nx (seq (case hi of
              Ex (CONST h) => if h < valOf Int.maxInt
                              then [MOVE (var', unEx lo),
                                    JUMP (NAME l2, [l2]),
                                    LABEL l1,
                                    unNx body,
                                    MOVE (var', BINOP (PLUS, var', CONST 1)),
                                    LABEL l2,
                                    CJUMP (GT, var', CONST h, lsal, l1),
                                    LABEL lsal]
                              else [MOVE (var', unEx lo),
                                    LABEL l2,
                                    CJUMP (EQ, var', CONST h, lsal, l1),
                                    unNx body,
                                    LABEL l1,
                                    MOVE (var', BINOP (PLUS, var', CONST 1)),
                                    JUMP (NAME l2, [l2]),
                                    LABEL lsal]
             | _         => let val t = newtemp()
                             in [MOVE (var', unEx lo),
                                MOVE (TEMP t, unEx hi),
                                unNx body,
                                CJUMP (EQ, var', TEMP t, lsal, l1),
                                LABEL l1,
                                MOVE (var', BINOP (PLUS, var', CONST 1)),
                                JUMP (NAME l2, [l2]),
                                LABEL lsal]
                            end))
  end

fun ifThenExp{test, then'} =
  let
    val tst = unCx test
    val (t,f) = (newlabel(), newlabel())
  in
    Nx (seq [tst(t,f),
            LABEL t,
            unNx then',
            LABEL f])
  end

fun ifThenElseExp {test,then',else'} =
  let
    val tst = unCx test
    val thenExp = unEx then'
    val elseExp = unEx else'
    val (t,f,lexit) = (newlabel(), newlabel(), newlabel())
    val r = newtemp()
  in
    Ex (ESEQ (seq [tst(t,f),
                  LABEL t,
                  MOVE(TEMP r, thenExp),
                  JUMP (NAME lexit, [lexit]),
                  LABEL f,
                  MOVE(TEMP r, elseExp),
                  JUMP (NAME lexit, [lexit]),
                  LABEL lexit], TEMP r))
  end

fun ifThenElseExpUnit {test,then',else'} =
  let
    val tst = unCx test
    val (t,f,lexit) = (newlabel(), newlabel(), newlabel())
    val r = newtemp()
  in
    Nx (seq [tst(t,f),
            LABEL t,
            unNx then',
            JUMP (NAME lexit, [lexit]),
            LABEL f,
            unNx else',
            JUMP (NAME lexit, [lexit]),
            LABEL lexit])
  end

fun assignExp{var, exp} =
let
  val v = unEx var
  val vl = unEx exp
in
  Nx (MOVE(v,vl))
end

fun binOpIntExp {left, oper, right} =
  let val l = unEx left
      val r = unEx right
  in case oper of
      PlusOp => Ex (BINOP (PLUS, l, r))
    |  MinusOp => Ex (BINOP (MINUS, l, r))
    |  DivideOp => Ex (BINOP (DIV, l, r))
    |  TimesOp => Ex (BINOP (MUL, l, r))
    | _       => raise Fail "shouldn't happen (binOpIntExp)"
  end

fun binOpIntRelExp {left,oper,right} =
  let val l = unEx left
      val r = unEx right
      fun subst(oper) = (fn (t,f) => CJUMP (oper, l, r, t, f))
  in case oper of
      EqOp => Cx (subst(EQ))
    | NeqOp => Cx (subst(NE))
    | LtOp => Cx (subst(LT))
    | LeOp => Cx (subst(LE))
    | GtOp => Cx (subst(GT))
    | GeOp => Cx (subst(GE))
    | _    => raise Fail "shouldn't happen (binOpIntRelExp)"
  end

fun binOpStrExp {left,oper,right} =
  let val l = unEx left
      val r = unEx right
      fun subst(oper) = (fn (t,f) => CJUMP (oper, ESEQ (EXP (externalCall ("_stringCompare", [l,r])),
                                                        TEMP rv),
                                            CONST 0, t, f))
  in case oper of
      EqOp  => Cx (subst(EQ))
    | NeqOp => Cx (subst(NE))
    | LtOp => Cx (subst(LT))
    | LeOp => Cx (subst(LE))
    | GtOp => Cx (subst(GT))
    | GeOp => Cx (subst(GE))
    | _     => raise Fail "shouldn't happen (binOpStrExp)"
  end
end
