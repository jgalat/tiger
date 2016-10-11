(*
  Frames para el 80386 (sin displays ni registers).

    |    argn    |  fp+4*(n+1)
    |    ...     |
    |    arg2    |  fp+16
    |    arg1    |  fp+12
    |  fp level |  fp+8
    |  retorno   |  fp+4
    |   fp ant   |  fp
    --------------  fp
    |   local1   |  fp-4
    |   local2   |  fp-8
    |    ...     |
    |   localn   |  fp-4*n
*)

structure tigerframe :> tigerframe = struct

open tigertree

type level = int

val fp = "%ebp"        (* frame pointer *)
val sp = "%esp"        (* stack pointer *)
val rv = "%eax"        (* return value  *)
val ov = "%edx"        (* overflow value (edx en el 386) *)
val si = "%esi"
val di = "%edi"
val bx = "%ebx"
val cx = "%ecx"
val dx = "%edx"
val ds = "%ds"
val es = "%es"
val ss = "%ss"
val wSz = 4            (* word size in bytes *)
val log2WSz = 2        (* base two logarithm of word size in bytes *)
val fpPrev = 0         (* offset (bytes) *)
val fpPrevLev = 8      (* offset (bytes) *)
val argsInicial = 2    (* words *)
val argsOffInicial = 1 (* words *)
val argsGap = wSz      (* bytes *)
val regInicial = 1     (* reg *)
val localsInicial = 0  (* words *)
val localsGap = ~1     (* words *)
val calldefs = [rv]
val specialregs = [rv, fp, sp]
val argregs = []
val callersaves = [rv, cx, dx]
val calleesaves = [di, si, bx, ds, es, ss]

type frame = {
  name: string,
  formals: bool list,
  locals: bool list,
  actualArg: int ref,
  actualLocal: int ref,
  actualReg: int ref
}
type register = string
datatype access = InFrame of int | InReg of tigertemp.label
datatype frag = PROC of {body: tigertree.stm, frame: frame}
  | STRING of tigertemp.label * string
fun newFrame{name, formals} = {
  name=name,
  formals=formals,
  locals=[],
  actualArg=ref argsInicial,
  actualLocal=ref localsInicial,
  actualReg=ref regInicial
}
fun name(f: frame) = #name f
fun string(l, s) = l^tigertemp.makeString(s)^"\n"
fun formals({formals=f, ...}: frame) =
  let  fun aux(n, []) = []
    | aux(n, h::t) = InFrame(n)::aux(n+argsGap, t)
  in aux(argsInicial * wSz, f) end
fun maxRegFrame(f: frame) = !(#actualReg f)
fun allocArg (f: frame) b =
  case b of
  true =>
    let val ret = (!(#actualArg f) + argsOffInicial) * wSz
        val _ = #actualArg f := !(#actualArg f)+1
    in InFrame ret end
  | false => InReg(tigertemp.newtemp())

fun allocLocal (f: frame) b =
  case b of
  true =>
    let val ret =  (!(#actualLocal f) + localsGap) * wSz
        val _ = #actualLocal f:=(!(#actualLocal f)-1);
    in  InFrame ret end
  | false => InReg(tigertemp.newtemp())
fun exp(InFrame k) e = MEM(BINOP(PLUS, TEMP(fp), CONST k))
| exp(InReg l) e = TEMP l
fun externalCall(s, l) = CALL(NAME s, l)

fun seq [] = EXP (CONST 0)
  | seq [s] = s
  | seq (x::xs) = SEQ (x, seq xs)

fun procEntryExit1 (frame, body) =
  let (* Ver si restaurar alrevés cuando sea haga push y pop *)
    val inFrames = List.map (fn _ => allocLocal frame true) calleesaves
    val calleesaves' = List.map TEMP calleesaves
    val saveCallee = List.map (fn (f, r) => MOVE (exp f (TEMP fp), r)) (ListPair.zip (inFrames, calleesaves'))
    val restoreCallee = List.map (fn (r, f) => MOVE (r, exp f (TEMP fp))) (ListPair.zip (calleesaves', inFrames))
  in
    seq (saveCallee @ [body] @ restoreCallee)
  end

fun procEntryExit3(body, frame) =
  let
    val prolog =".globl "^ name frame ^ "\n"
              ^ name frame ^ ":\n"
              ^ "\tenter 0, " ^ Int.toString (abs(!(#actualLocal frame)) * wSz) ^"\n"
    val epilog = "\tleave\n\tret\n\n"
  in
    {prolog = prolog, body = body, epilog = epilog}
  end
end
