structure tigerseman :> tigerseman =
struct

open tigerabs
open tigersres
open tigertrans

type expty = {exp: unit, ty: Tipo}

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList(
	tabNueva(),
	[("int", TInt), ("string", TString)])

val levelPila: tigertrans.level tigerpila.Pila = tigerpila.nuevaPila1(tigertrans.outermost)
fun pushLevel l = tigerpila.pushPila levelPila l
fun popLevel() = tigerpila.popPila levelPila
fun topLevel() = tigerpila.topPila levelPila

val tab_vars : (string, EnvEntry) Tabla = tabInserList(
	tabNueva(),
	[("print", Func{level=topLevel(), label="print",
		formals=[TString], result=TUnit, extern=true}),
	("flush", Func{level=topLevel(), label="flush",
		formals=[], result=TUnit, extern=true}),
	("getchar", Func{level=topLevel(), label="getstr",
		formals=[], result=TString, extern=true}),
	("ord", Func{level=topLevel(), label="ord",
		formals=[TString], result=TInt, extern=true}),
	("chr", Func{level=topLevel(), label="chr",
		formals=[TInt], result=TString, extern=true}),
	("size", Func{level=topLevel(), label="size",
		formals=[TString], result=TInt, extern=true}),
	("substring", Func{level=topLevel(), label="substring",
		formals=[TString, TInt, TInt], result=TString, extern=true}),
	("concat", Func{level=topLevel(), label="concat",
		formals=[TString, TString], result=TString, extern=true}),
	("not", Func{level=topLevel(), label="not",
		formals=[TInt], result=TInt, extern=true}),
	("exit", Func{level=topLevel(), label="exit",
		formals=[TInt], result=TUnit, extern=true})
	])

fun tipoReal (TTipo (s, ref (SOME t))) = t
  | tipoReal (TTipo (s, ref NONE)) = raise Fail (s^" is NONE!")
  | tipoReal t = t

	fun tiposIguales (TRecord _) TNil = true
  | tiposIguales TNil (TRecord _) = true
  | tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = (u1=u2)
  | tiposIguales (TArray (_, u1)) (TArray (_, u2)) = (u1=u2)
  | tiposIguales (a as (TTipo _)) b = tiposIguales (tipoReal a) b
  | tiposIguales a (b as (TTipo _)) = tiposIguales a (tipoReal b)
  | tiposIguales a b = (a=b)

fun transExp(venv, tenv) =
	let fun error(s, p) = raise Fail ("Error -- line "^Int.toString(p)^": "^s^"\n")
		fun trexp(VarExp v) = trvar(v)
		| trexp(UnitExp _) = {exp=unitExp(), ty=TUnit}
		| trexp(NilExp _)= {exp=nilExp(), ty=TNil}
		| trexp(IntExp(i, _)) = {exp=intExp(i), ty=TInt}
		| trexp(StringExp(s, _)) = {exp=stringExp(s), ty=TString}
		| trexp(CallExp({func, args}, nl)) =
				let
						val (tArgs, ext, tRet, lab, lvl) = case tabBusca (func, venv) of
								 SOME (Func {formals, extern, result, label, level})  => (formals, extern, result, label, level)
								|SOME _ => error(func^": is not a function", nl)
								|NONE   => error(func^": not defined", nl)
						fun aux [] [] r = r
							 |aux [] _ r  = error("too many arguments", nl)
							 |aux _ [] r  = error("few arguments", nl)
							 |aux (x::xs) (y::ys) r = let val {exp = expY, ty = tY} = trexp y
																						val _ = if tiposIguales x tY
																										then ()
																										else error("incorrect types", nl)
																				in aux xs ys r@[{exp = expY, ty = tY}]
																				end
						val leArgs  = aux tArgs args []
						val leArgs' = map #exp leArgs
						val pf      = tRet = TUnit
				in
						{exp = callExp(lab, ext, pf, lvl, leArgs'), ty = tRet}
				end
		| trexp(OpExp({left, oper=EqOp, right}, nl)) =
			let
				val {exp=expl, ty=tyl} = trexp left
				val {exp=expr, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso not(tiposIguales tyl TUnit) then
					{exp=if tiposIguales tyl TString then binOpStrExp {left=expl,oper=EqOp,right=expr} else binOpIntRelExp {left=expl,oper=EqOp,right=expr}, ty=TInt}
					else error("incomparable types", nl)
			end
		| trexp(OpExp({left, oper=NeqOp, right}, nl)) =
			let
				val {exp=expl, ty=tyl} = trexp left
				val {exp=expr, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso not(tiposIguales tyl TUnit) then
					{exp=if tiposIguales tyl TString then binOpStrExp {left=expl,oper=NeqOp,right=expr} else binOpIntRelExp {left=expl,oper=NeqOp,right=expr}, ty=TInt}
					else error("incomparable types", nl)
			end
		| trexp(OpExp({left, oper, right}, nl)) =
			let
				val {exp=expl, ty=tyl} = trexp left
				val {exp=expr, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr then
					case oper of
						PlusOp => if tiposIguales tyl TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Type error", nl)
						| MinusOp => if tiposIguales tyl TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Type error", nl)
						| TimesOp => if tiposIguales tyl TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Type error", nl)
						| DivideOp => if tiposIguales tyl TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Type error", nl)
						| LtOp => if  tiposIguales tyl TInt orelse tiposIguales tyl TString then
							{exp=if tiposIguales tyl TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt}
							else error("Type error", nl)
						| LeOp => if tiposIguales tyl TInt orelse tiposIguales tyl TString then
							{exp=if tiposIguales tyl TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt}
							else error("Type error", nl)
						| GtOp => if tiposIguales tyl TInt orelse tiposIguales tyl TString then
							{exp=if tiposIguales tyl TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt}
							else error("Type error", nl)
						| GeOp => if tiposIguales tyl TInt orelse tiposIguales tyl TString then
							{exp=if tiposIguales tyl TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt}
							else error("Type error", nl)
						| _ => error("shouldn't happen! (3)", nl)
				else error("Type error", nl)
			end
		| trexp(RecordExp({fields, typ}, nl)) =
			let
				(* Traducir cada expresión de fields *)
				val tfields = map (fn (sy,ex) => (sy, trexp ex)) fields

				(* Buscar el tipo *)
				val (tyr, cs) = case tabBusca(typ, tenv) of
					SOME t => (case tipoReal t of
											TRecord (cs, u) => (TRecord (cs, u), cs)
											| _ => error(typ^" isn't a record type", nl))
					| NONE => error("Type \""^typ^"\" doesn't exist", nl)

				(* Verificar que cada campo esté en orden y tenga una expresión del tipo que corresponde *)
				(* Possible TODO: unordered fields *)
				fun verificar _ [] [] = []
				  | verificar _ (c::cs) [] = error("missing fields", nl)
				  | verificar _ [] (c::cs) = error("spare fields", nl)
				  | verificar n ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
						if s<>sy then error("field error", nl)
						else if tiposIguales ty t then (exp, n)::(verificar (n+1) cs ds)
							 else error("field's type error "^s, nl)
				val lf = verificar 0 cs tfields
			in
				{exp=recordExp(lf), ty=tyr}
			end
		| trexp(SeqExp(s, nl)) =
			let	val lexti = map trexp s
				val exprs = map (fn{exp, ty} => exp) lexti
				val {exp, ty=tipo} = hd(rev lexti)
			in	{ exp=seqExp (exprs), ty=tipo } end
		| trexp(AssignExp({var=SimpleVar s, exp}, nl)) =
			let val _ = (case tabBusca (s, venv) of
								NONE => error(s^": variable is not in scope", nl)
							| SOME (VIntro _) => error(s^": read only variable", nl)
							| SOME (Func _)   => error(s^": assigning an expression to a function", nl)
							| _               => ())
					val {exp = expVar, ty=typVar} = trvar (SimpleVar s, nl)
					val {exp = expExp, ty=typExp} = trexp exp
			in if tiposIguales typVar typExp
						then {exp = assignExp{var = expVar, exp = expExp}, ty=TUnit}
						else error (s^": Types do not match", nl)
			end
		| trexp(AssignExp({var, exp}, nl)) =
			let val {exp = expVar, ty = typVar} = trvar (var, nl)
					val {exp = expExp, ty = typExp} = trexp exp
			in
					if tiposIguales typVar typExp
							then {exp = assignExp{var = expVar, exp = expExp}, ty = TUnit}
							else error("Types do not match", nl)
			end
		| trexp(IfExp({test, then', else'=SOME else'}, nl)) =
			let val {exp=testexp, ty=tytest} = trexp test
			    val {exp=thenexp, ty=tythen} = trexp then'
			    val {exp=elseexp, ty=tyelse} = trexp else'
			in
				if tiposIguales tytest TInt andalso tiposIguales tythen tyelse then
				{exp=if tiposIguales tythen TUnit then ifThenElseExpUnit {test=testexp,then'=thenexp,else'=elseexp} else ifThenElseExp {test=testexp,then'=thenexp,else'=elseexp}, ty=tythen}
				else error("Type error" ,nl)
			end
		| trexp(IfExp({test, then', else'=NONE}, nl)) =
			let val {exp=exptest,ty=tytest} = trexp test
			    val {exp=expthen,ty=tythen} = trexp then'
			in
				if tiposIguales tytest TInt andalso tiposIguales tythen TUnit then
				{exp=ifThenExp{test=exptest, then'=expthen}, ty=TUnit}
				else error("Type error", nl)
			end
		| trexp(WhileExp({test, body}, nl)) =
			let
				val _ = preWhileForExp()
				val {exp=etest, ty=ttest} = trexp test
				val {exp=ebody, ty=tbody} = trexp body
				val wExp = whileExp {test=etest, body=ebody, lev=topLevel()}
				val _ = postWhileForExp()
			in
				if tiposIguales ttest TInt andalso tiposIguales tbody TUnit then {exp=wExp , ty=TUnit}
				else if not(tiposIguales ttest TInt) then error("type error in condition", nl)
				else error("body should be unit type", nl)
			end
		| trexp(ForExp({var, escape, lo, hi, body}, nl)) =
			let val {exp = expHi, ty = typHi} = trexp hi
					val {exp = expLo, ty = typLo} = trexp lo
					val _ = if tiposIguales typLo TInt andalso tiposIguales typHi TInt then () else error("boundaries not Int", nl)
					val acc' = allocLocal (topLevel()) (!escape)
					val lvl = getActualLev()
					val _ = preWhileForExp()
					val venv' = fromTab venv
					val venv'' = tabInserta (var, VIntro {access = acc', level = lvl}, venv')
					val {exp = expBody, ty = typBody} = transExp (venv'', tenv) body
					val ev' = simpleVar(acc', lvl)
					val fExp = forExp{lo = expLo, hi = expHi, var = ev', body = expBody}
					val _ = postWhileForExp()
			in
					if tiposIguales typBody TUnit then {exp = fExp, ty = TUnit} else error("incorrect Type", nl)
			end
		| trexp(LetExp({decs, body}, _)) =
			let
				fun aux (d, (v, t, exps1)) =
				let
					val (v', t', exps2) = trdec (v, t) d
				in
					(v', t', exps1@exps2)
				end
				val (venv', tenv', expdecs) = List.foldl aux (venv, tenv, []) decs
				val {exp=expbody,ty=tybody}=transExp (venv', tenv') body
			in
				{exp=seqExp(expdecs@[expbody]), ty=tybody}
			end
		| trexp(BreakExp nl) =
			{exp=breakExp() handle _ => error("break outside of loop", nl), ty=TUnit}
		| trexp(ArrayExp({typ, size, init}, nl)) =
			let val typ = (case tabBusca(typ, tenv) of
												SOME (TArray (t, u)) => (t,u)
												| SOME _ => error(typ^": is not an array", nl)
												| _  => error(typ^": undefined type", nl))
					val {exp = initExp, ty = typInit} = trexp init
					val _ = if tiposIguales typInit (#1 typ)
										then ()
										else error("types do not match", nl)
					val {exp = sizeExp, ty = typSize} = trexp size
					val _ = if tiposIguales typSize TInt
										then ()
										else error("size isn't integer", nl)
			in {exp = arrayExp{init=initExp, size=sizeExp}, ty = TArray typ}
			end
		and trvar(SimpleVar s, nl) =
			(case tabBusca(s, venv) of
						NONE        => error(s^": undefined variable", nl)
					| SOME (VIntro {access = acc, level = lvl}) => {exp = simpleVar(acc, lvl), ty = TInt}
					| SOME (Var {ty=t, access = acc, level = lvl}) => {exp = simpleVar(acc, lvl) , ty = t}
					| SOME _      => error(s^": is a function, not a variable", nl))
		| trvar(FieldVar(v, s), nl) =
			let val {exp = varExp, ty = tyv} = trvar (v, nl)
					val lflds = case tipoReal tyv of
													TRecord (l,_)  =>  l
													| _ => error("variable is not a record", nl)
					val (tr,nc) =  case List.find (fn (n, _, _) => n = s) lflds of
													 SOME (_,tyf, n) => (tyf, n)
													 | _ => error(s^": inexistent field in record",nl)
			in {exp = fieldVar(varExp, nc), ty = tipoReal tr}
			end
		| trvar(SubscriptVar(v, e), nl) =
			let val {exp = varExp, ty = tyv} 	= trvar(v, nl)
					val {exp = expExp, ty = tyexp} = trexp e
					val tr = (case tipoReal tyv of
												TArray (t, _) => t
											| _             => error("variable is not an array", nl))
			in 	if tiposIguales tyexp TInt then {exp = subscriptVar(varExp, expExp), ty = tr}
					else error("index is not integer", nl)
			end
			and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},pos)) =
	      let val {exp = initExp, ty = typInit} = transExp (venv, tenv) init
	          val _ = if typInit=TNil then error("variable with no explicit type is type nil", pos) else ()
						val acc = allocLocal (topLevel()) (!escape)
						val lvl = getActualLev()
	          val venv' = tabRInserta (name, Var {ty = typInit, access = acc, level = lvl}, venv)
	      in (venv', tenv, [varDec(acc, initExp)])
				end
    | trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},pos)) =
      let val {exp = initExp, ty = typInit} = transExp (venv, tenv) init
          val tt = (case tabBusca (s, tenv) of
                      SOME t => t
                      | NONE => error(s^": undefined type", pos))
          val _ = if tiposIguales tt typInit then () else error("non-matching types", pos)
					val acc = allocLocal (topLevel()) (!escape)
					val lvl = getActualLev()
					val venv' = tabRInserta (name, Var {ty = tt, access = acc, level = lvl}, venv)
      in (venv', tenv, [varDec(acc, initExp)])
			end
    | trdec (venv,tenv) (FunctionDec []) =
      (venv, tenv, [])
    | trdec (venv,tenv) (FunctionDec fs) =
      let val nl = #2 (List.hd fs)
          fun reps [] = false
          | reps ({name,...}::t) = if List.exists (fn {name = x,...} => x = name) t then true else reps t
          fun FDecToFEntry {name, params, result, body} =
            let val stringFormal = List.map #typ params
                val formal = List.map (fn (NameTy s) => (case tabBusca (s, tenv) of
                                                          SOME t => t
                                                          |NONE => error(s^": undefined type", nl))
                                      | _ => TUnit) stringFormal
                val resType = case result of
                    SOME t => (case tabBusca(t, tenv) of
                                SOME tt => tt
                                |NONE => error(t^": undefined type", nl))
                    |NONE => TUnit
								val label = tigertemp.newlabel()
								val realName = if name = "_tigermain" then "_tigermain" else name ^ "_" ^ label
            in Func { level = newLevel{parent=topLevel(), name=realName, formals= true :: List.map (! o #escape) params},
											label = realName,
											formals = formal,
											result = resType,
											extern = false}
						end
          val fs' = List.map #1 fs
          val _ = if reps fs' then error("repeated names in batch declaration", nl) else ()
          val fEntries = List.map FDecToFEntry fs'
          val fNameEntry = ListPair.zip (List.map #name fs', fEntries)
          val venv' = List.foldl (fn (f,tab) => tabRInserta (#1 f, #2 f, tab)) venv fNameEntry
          val fDecFEntry = ListPair.zip(fs', fEntries)

					fun trexpBodyNCompare ({params, body, ...}, Func {formals, result, level, ... }) =
            let val vt = ListPair.zip(params, formals)

						    val _ = preFunctionDec()
								val _ = pushLevel level
                val venv'' = List.foldl (fn ((v,t),e) =>
																					tabRInserta (#name v,
																											Var {ty=t,
																													access = allocArg (level) true (* (!(#escape v)) *),
																													level = getActualLev()},
																											 e)) venv' vt
								val {exp = expBody, ty = typBody} = transExp (venv'', tenv) body
								val interCode = functionDec(expBody, level, tiposIguales result TUnit)
								val _ = popLevel()
								val _ = postFunctionDec()
						in if tiposIguales typBody result
                then interCode
                else error("function body type doesn't match result type", nl)
            end
              | trexpBodyNCompare _ = error("shouldn't happen (4)", nl)

					val interCodeBodies = List.map trexpBodyNCompare fDecFEntry
      in (venv', tenv, interCodeBodies)
			end
    | trdec (venv,tenv) (TypeDec []) =
      (venv, tenv, [])
    | trdec (venv, tenv) (TypeDec ts) =
      let val nl = #2 (List.hd ts)
          fun reps [] = false
          | reps ({name,...}::t) = if List.exists (fn {name = x,...} => x = name) t then true else reps t
          val ts' = map #1 ts
          val _ = if reps ts' then error("repeated names in batch declaration", nl) else ()
          val tenv' = (tigertopsort.fijaTipos ts' tenv) handle tigertopsort.Ciclo => error("Cycle", nl)
      in (venv, tenv', [])
			end
	in trexp end
fun transProg ex =
	let	val main =
				LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
								result=SOME "int", body=ex}, 0)]],
						body=UnitExp 0}, 0)
		val _ = transExp(tab_vars, tab_tipos) main
	in	print "good!\n" end
end
