open tigerlex
open tigergrm
open tigerescap
open tigerseman
open BasicIO Nonstdio

fun lexstream(is: instream) =
  Lexing.createLexer(fn b => fn n => buff_input is b 0 n);
fun errParsing(lbuf) = (print("Parsing error!("
  ^(makestring(!num_linea))^
  ")["^(Lexing.getLexeme lbuf)^"]\n"); raise Fail "done!")
fun main(args) =
  let  fun arg(l, s) =
      (List.exists (fn x => x=s) l, List.filter (fn x => x<>s) l)
    val (arbol, l1)    = arg(args, "-tree")
    val (escapes, l2)  = arg(l1, "-escapes")
    val (ir, l3)    = arg(l2, "-go")
    val (canonOp, l4)    = arg(l3, "-canon")
    val (code, l5)    = arg(l4, "-code")
    val (flow, l6)    = arg(l5, "-flow")
    val (inter, l7)    = arg(l6, "-interp")
    val entrada =
      case l7 of
      [n] => ((open_in n)
          handle _ => raise Fail (n^" doesn't exist!"))
      | [] => std_in
      | _ => raise Fail "unknown option!"
    val lexbuf = lexstream entrada
    val expr = prog Tok lexbuf handle _ => errParsing lexbuf
    val _ = if arbol then tigerpp.exprAst expr else ()
    val _ = findEscape(expr)
    val _ = transProg(expr)
		val fragmentos = tigertrans.getResult()
    val canon = (tigercanon.traceSchedule o tigercanon.basicBlocks o tigercanon.linearize)
    fun divideFrags [] = ([],[])
      | divideFrags (tigerframe.PROC {body,frame} :: t) =
          let val (stm,str) = divideFrags t
          in ((canon body,frame)::stm,str)
          end
      | divideFrags (tigerframe.STRING (lab,st) :: t) =
          let val (stm,str) = divideFrags t
          in (stm,(lab,st)::str)
          end
    val (canonizado, strings) = divideFrags fragmentos
    val _ = if canonOp
          then (List.app (fn (l,s) =>  print ("LABEL " ^ l ^ " STRING " ^ s ^ "\n")) strings;
                List.app (fn (c, f) => (print ("\n"^(tigerframe.name f)^":\n"); List.app (print o tigerit.tree) c)) canonizado)
          else ()
    val _ = if inter then tigerinterp.inter inter canonizado strings else ()
  in
    print "Y!!\n"
  end  handle Fail s => print("Fail: "^s^"\n")

val _ = main(CommandLine.arguments())
