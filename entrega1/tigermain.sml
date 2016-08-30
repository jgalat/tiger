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
    val (canon, l4)    = arg(l3, "-canon")
    val (code, l5)    = arg(l4, "-code")
    val (flow, l6)    = arg(l5, "-flow")
    val (inter, l7)    = arg(l6, "-interp")
    val entrada =
      case l7 of
      [n] => ((open_in n)
          handle _ => raise Fail (n^" doesn't exist!"))
      | [] => std_in
      | _ => raise Fail "Unknown option"
    val lexbuf = lexstream entrada
    val expr = prog Tok lexbuf handle _ => errParsing lexbuf
    (* val _ = findEscape(expr) *)
    val _ = if arbol then tigerpp.exprAst expr else ()
  in
    transProg(expr);
    print "Y\n"
  end  handle Fail s => print("Fail: "^s^"\n")

val _ = main(CommandLine.arguments())
