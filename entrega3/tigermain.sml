open tigerlex
open tigergrm
open tigerescap
open tigerseman
open tigerflowgraph
open tigerliveness
open BasicIO Nonstdio
open Process

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
    val (ir, l3)       = arg(l2, "-go")
    val (canonOp, l4)  = arg(l3, "-canon")
    val (code, l5)     = arg(l4, "-code")
    val (flow, l6)     = arg(l5, "-flow")
    val (inter, l7)    = arg(l6, "-interp")
    val (igraph, l8)   = arg(l7, "-igraph")
    val (asmO, l9)     = arg(l8, "-asm")
    val entrada =
      case l9 of
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
    val (canonized, strings) = divideFrags fragmentos
    (*val canonizedFolded = List.map (fn (b, f) => (tigerfold.constFolding b, f)) canonized *)
    val _ = if canonOp
          then (List.app (fn (l,s) =>  print ("LABEL " ^ l ^ " STRING " ^ s ^ "\n")) strings;
                List.app (fn (c, f) => (print ("\n"^(tigerframe.name f)^":\n"); List.app (print o tigerit.tree) c)) canonized)
          else ()
    val _ = if inter then tigerinterp.inter inter canonized strings else ()
    val asm = List.map ( fn (b,f) =>
                          let
                            val asm = List.concat (List.map (tigercodegen.codegen f) b)
                            val pbe = tigerframe.procEntryExit3 (asm, f)
                          in (pbe, f)
                          end ) canonized
    fun prtCode ({prolog, body, epilog}, _) =
      let
        val str = List.map (tigerassem.format tigertab.name) body
        val _ = (print prolog; List.map print str; print epilog)
      in () end

    fun iGraphs ({body, ...}, f) =
      let
        val (g, l) = makeGraph body
        val (igraph, _) = interferenceGraph g
      in (igraph, f) end

    val _ = if code then List.app prtCode asm else ()
    val igraphs = if igraph then List.map iGraphs asm else []

    fun appShowDot (i, f) = tigerliveness.showDot i (tigerframe.name f)
    val _ = List.map appShowDot igraphs

    fun prtCodeColored out ({prolog, body, epilog}, frame) =
      let
        val (allocation, newbody) = tigercolor.alloc(body, frame)
        fun saytemp s = Splaymap.find(allocation, s)
        fun xd x = case Char.toString x of
                      "~" => (case Char.fromString "-" of
                              SOME c => c
                              | _    => raise Fail "Shouldn't happen (prtCodeColored)")
                    | _ => x
        val str = List.map (tigerassem.format saytemp) newbody
        val str = List.map (String.map xd) str
        val _ = if asmO then (print "\n"; print prolog; List.map print str; print epilog; print "\n") else ()
        val _ = (output (out, prolog); List.map (fn s => output(out, s)) str; output (out, epilog))
      in () end

    fun prtString out (label, str) =
    let
      val _ = output (out, label^": ")
      val _ = if asmO then print (label ^ ": ") else ()
      val _ = output (out, str^"\n")
      val _ = if asmO then print (str ^ "\n" ) else ()
    in () end


    fun genAsm () =
      let
        val outfile = open_out "tigermain.s"
        val _ = output(outfile, ".data\n")
        val _ = List.map (prtString outfile) strings
        val _ = output(outfile, ".text\n")
        val _ = List.map (prtCodeColored outfile) asm
        val _ = close_out outfile
      in () end

    val _ = genAsm ()
    val x = system "gcc runtime.c tigermain.s -m32 -g"
  in
    if isSuccess x
    then print "yeaboi!!\n"
    else print "nooboi!!\n"
  end  handle Fail s => print("Fail: "^s^"\n")

val _ = main(CommandLine.arguments())
