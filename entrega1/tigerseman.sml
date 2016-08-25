structure tigerseman :> tigerseman =
struct

open tigerabs
open tigersres

type expty = {exp: unit, ty: Tipo}

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList(
	tabNueva(),
	[("int", TInt), ("string", TString)])

val tab_vars : (string, EnvEntry) Tabla = tabInserList(
	tabNueva(),
	[("print", Func{level=mainLevel, label="print",
		formals=[TString], result=TUnit, extern=true}),
	("flush", Func{level=mainLevel, label="flush",
		formals=[], result=TUnit, extern=true}),
	("getchar", Func{level=mainLevel, label="getstr",
		formals=[], result=TString, extern=true}),
	("ord", Func{level=mainLevel, label="ord",
		formals=[TString], result=TInt, extern=true}),
	("chr", Func{level=mainLevel, label="chr",
		formals=[TInt], result=TString, extern=true}),
	("size", Func{level=mainLevel, label="size",
		formals=[TString], result=TInt, extern=true}),
	("substring", Func{level=mainLevel, label="substring",
		formals=[TString, TInt, TInt], result=TString, extern=true}),
	("concat", Func{level=mainLevel, label="concat",
		formals=[TString, TString], result=TString, extern=true}),
	("not", Func{level=mainLevel, label="not",
		formals=[TInt], result=TInt, extern=true}),
	("exit", Func{level=mainLevel, label="exit",
		formals=[TInt], result=TUnit, extern=true})
	])

fun tipoReal (TTipo s, (env : tenv)) : Tipo =
    (case tabBusca(s , env) of
         NONE => raise Fail "typeReal TType"
       | SOME t => t)
  | tipoReal (t, _) = t

	fun tiposIguales (TRecord _) TNil = true
  | tiposIguales TNil (TRecord _) = true
  | tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = (u1=u2)
  | tiposIguales (TArray (_, u1)) (TArray (_, u2)) = (u1=u2)
  | tiposIguales (TTipo _) b =
		(* let *)
		(* 	val a = case !r of *)
		(* 		SOME t => t *)
		(* 		| NONE => raise Fail "No debería pasar! (1)" *)
		(* in *)
		(* 	tiposIguales a b *)
		(* end *)raise Fail "Shouldn't happen! (1)"
  | tiposIguales a (TTipo _) =
		(* let *)
		(* 	val b = case !r of *)
		(* 		SOME t => t *)
		(* 		| NONE => raise Fail "No debería pasar! (2)" *)
		(* in *)
		(* 	tiposIguales a b *)
		(* end *)raise Fail "Shouldn't happen! (2)"
  | tiposIguales a b = (a=b)

fun isInt TInt = true
    |isInt _    = false

fun transExp(venv, tenv) =
	let fun error(s, p) = raise Fail ("Error -- line "^Int.toString(p)^": "^s^"\n")
		fun trexp(VarExp v) = trvar(v)
		| trexp(UnitExp _) = {exp=(), ty=TUnit}
		| trexp(NilExp _)= {exp=(), ty=TNil}
		| trexp(IntExp(i, _)) = {exp=(), ty=TInt}
		| trexp(StringExp(s, _)) = {exp=(), ty=TString}
		| trexp(CallExp({func, args}, nl)) = 
            let
                val (tArgs, ext, tRet, lab, lvl) = case tabBusca (func, venv) of
                     SOME (Func {formals, extern, result, label, level})  => (formals, extern, result, label, level)
                    |SOME _ => error(func^": Is not a function", nl)
                    |NONE   => error(func^": Not defined", nl)
                fun aux [] [] r = r
                   |aux [] _ r  = error("Too many arguments", nl)
                   |aux _ [] r  = error("Few arguments", nl)
                   |aux (x::xs) (y::ys) r = let val {exp = expY, ty = tY} = trexp y
                                                val _ = tiposIguales x tY
                                                        handle _ => error("Incorrect types", nl)
                                            in aux xs ys r@[{exp = expY, ty = tY}]
                                            end
                val leArgs  = aux tArgs args []
                val leArgs' = map #exp leArgs
                val pf      = tRet = TUnit
            in
                {exp = (), ty = tRet}
            end
		| trexp(OpExp({left, oper=EqOp, right}, nl)) =
			let
				val {exp=_, ty=tyl} = trexp left
				val {exp=_, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=(), ty=TInt}
					else error("Incomparable types", nl)
			end
		| trexp(OpExp({left, oper=NeqOp, right}, nl)) =
			let
				val {exp=_, ty=tyl} = trexp left
				val {exp=_, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=(), ty=TInt}
					else error("Incomparable types", nl)
			end
		| trexp(OpExp({left, oper, right}, nl)) =
			let
				val {exp=_, ty=tyl} = trexp left
				val {exp=_, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr then
					case oper of
						PlusOp => if tipoReal(tyl, tenv)=TInt then {exp=(),ty=TInt} else error("Type error", nl)
						| MinusOp => if tipoReal(tyl,tenv)=TInt then {exp=(),ty=TInt} else error("Type error", nl)
						| TimesOp => if tipoReal(tyl,tenv)=TInt then {exp=(),ty=TInt} else error("Type error", nl)
						| DivideOp => if tipoReal(tyl,tenv)=TInt then {exp=(),ty=TInt} else error("Type error", nl)
						| LtOp => if tipoReal(tyl,tenv)=TInt orelse tipoReal(tyl,tenv)=TString then {exp=(),ty=TInt} else error("Type error", nl)
						| LeOp => if tipoReal(tyl,tenv)=TInt orelse tipoReal(tyl,tenv)=TString then {exp=(),ty=TInt} else error("Type error", nl)
						| GtOp => if tipoReal(tyl,tenv)=TInt orelse tipoReal(tyl,tenv)=TString then {exp=(),ty=TInt} else error("Type error", nl)
						| GeOp => if tipoReal(tyl,tenv)=TInt orelse tipoReal(tyl,tenv)=TString then {exp=(),ty=TInt} else error("Type error", nl)
						| _ => raise Fail "Shouldn't happen! (3)"
				else error("Type error", nl)
			end
		| trexp(RecordExp({fields, typ}, nl)) =
			let
				(* Traducir cada expresión de fields *)
				val tfields = map (fn (sy,ex) => (sy, trexp ex)) fields

				(* Buscar el tipo *)
				val (tyr, cs) = case tabBusca(typ, tenv) of
					SOME t => (case tipoReal(t,tenv) of
						TRecord (cs, u) => (TRecord (cs, u), cs)
						| _ => error(typ^" isn't a record type", nl))
					| NONE => error("Type \""^typ^"\" doesn't exist", nl)

				(* Verificar que cada campo esté en orden y tenga una expresión del tipo que corresponde *)
				fun verificar [] [] = ()
				  | verificar (c::cs) [] = error("Missing fields", nl)
				  | verificar [] (c::cs) = error("Spare fields", nl)
				  | verificar ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
						if s<>sy then error("Field error", nl)
						else if tiposIguales ty (!t) then verificar cs ds
							 else error("Field's type error "^s, nl)
				val _ = verificar cs tfields
			in
				{exp=(), ty=tyr}
			end
		| trexp(SeqExp(s, nl)) =
			let	val lexti = map trexp s
				val exprs = map (fn{exp, ty} => exp) lexti
				val {exp, ty=tipo} = hd(rev lexti)
			in	{ exp=(), ty=tipo } end
		| trexp(AssignExp({var = SimpleVar s, exp}, nl)) =
				let val _ = (case tabBusca (s, venv) of
									NONE => error(s^": Variable is not in scope", nl)
									|SOME VIntro 		=> error(s^": Read only variable", nl)
									|SOME (Func _) 	=> error(s^": Assigning an expression to a function", nl)
									| _ 						=> ())
						val {exp = _, ty=typVar} = trvar (SimpleVar s, nl)
						val {exp = _, ty=typExp} = trexp exp
				in if tiposIguales typVar typExp
					 		then {exp = (), ty = TUnit}
							else error (s^": Types do not match", nl)
				end
		| trexp(AssignExp({var, exp}, nl)) = 
                let val {exp = _, ty = typVar} = trvar (var, nl)
                    val {exp = _, ty = typExp} = trexp exp
                in
                    if tiposIguales typVar typExp
                        then {exp = (), ty = TUnit}
                        else error("Types do not match", nl)
                end                     
		| trexp(IfExp({test, then', else'=SOME else'}, nl)) =
			let val {exp=testexp, ty=tytest} = trexp test
			    val {exp=thenexp, ty=tythen} = trexp then'
			    val {exp=elseexp, ty=tyelse} = trexp else'
			in
				if tipoReal(tytest,tenv)=TInt andalso tiposIguales tythen tyelse then {exp=(), ty=tythen}
				else error("Type error" ,nl)
			end
		| trexp(IfExp({test, then', else'=NONE}, nl)) =
			let val {exp=exptest,ty=tytest} = trexp test
			    val {exp=expthen,ty=tythen} = trexp then'
			in
				if tipoReal(tytest,tenv)=TInt andalso tythen=TUnit then {exp=(), ty=TUnit}
				else error("Type error", nl)
			end
		| trexp(WhileExp({test, body}, nl)) =
			let
				val {exp = exptest, ty = ttest} = trexp test
				val {exp = expbody, ty = tbody} = trexp body
			in
				if tipoReal(ttest, tenv) = TInt andalso tbody = TUnit then {exp=(), ty=TUnit}
				else if tipoReal(ttest, tenv) <> TInt then error("Type error in condition", nl)
				else error("Body should be unit type", nl)
			end
		| trexp(ForExp({var, escape, lo, hi, body}, nl)) =
            let val {exp = _, ty = typHi} = trexp hi
                val {exp = _, ty = typLo} = trexp lo
                val _ = if isInt typLo andalso isInt typHi then () else error("Boundaries not Int", nl)
                val venv' = fromTab venv
                val _ = tabInserta (var, VIntro, venv')
                val {exp = _, ty = typBody} = transExp (venv', tenv) body
            in
                if typBody = TUnit then {exp = (), ty = TUnit} else error("Incorrect Type", nl)
            end
		| trexp(LetExp({decs, body}, _)) =
			let
				val (venv', tenv', _) = List.foldl (fn (d, (v, t, _)) => trdec(v, t) d) (venv, tenv, []) decs
				val {exp=expbody,ty=tybody}=transExp (venv', tenv') body
			in
				{exp=(), ty=tybody}
			end
		| trexp(BreakExp nl) =
			{exp=(), ty=TUnit} (*COMPLETAR*)
		| trexp(ArrayExp({typ, size, init}, nl)) =
			{exp=(), ty=TUnit} (*COMPLETAR*)
		and trvar(SimpleVar s, nl) =
(*					case tabBusca(s, venv) of
							NONE 					=> error(s^": Undefined variable", nl)
							| SOME typVar => if tiposIguales(typVar, trexp exp)
																	then {exp=(), ty = typVar}
																	else error(s^": Types do not match", nl) *)
			{exp=(), ty=TUnit} (*COMPLETAR*)
		| trvar(FieldVar(v, s), nl) =
			{exp=(), ty=TUnit} (*COMPLETAR*)
		| trvar(SubscriptVar(v, e), nl) =
			{exp=(), ty=TUnit} (*COMPLETAR*)
		and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},pos)) =
			(venv, tenv, []) (*COMPLETAR*)
		| trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},pos)) =
			(venv, tenv, []) (*COMPLETAR*)
		| trdec (venv,tenv) (FunctionDec fs) =
			(venv, tenv, []) (*COMPLETAR*)
		| trdec (venv,tenv) (TypeDec ts) =
			(venv, tenv, []) (*COMPLETAR*)
	in trexp end
fun transProg ex =
	let	val main =
				LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
								result=SOME "int", body=ex}, 0)]],
						body=UnitExp 0}, 0)
		val _ = transExp(tab_vars, tab_tipos) main
	in	print "good!\n" end
end
