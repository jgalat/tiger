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

fun zip [] _ = []
  | zip _ [] = []
  | zip (h::t) (k::l) = (h,k)::(zip t l)

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
    | trexp(UnitExp _) = {exp=(), ty=TUnit}
    | trexp(NilExp _)= {exp=(), ty=TNil}
    | trexp(IntExp(i, _)) = {exp=(), ty=TInt}
    | trexp(StringExp(s, _)) = {exp=(), ty=TString}
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
            {exp = (), ty = tRet}
        end
    | trexp(OpExp({left, oper=EqOp, right}, nl)) =
      let
        val {exp=_, ty=tyl} = trexp left
        val {exp=_, ty=tyr} = trexp right
      in
        if tiposIguales tyl tyr andalso not(tyl=TNil andalso tyr=TNil) andalso not(tiposIguales tyl TUnit)
          then {exp=(), ty=TInt}
          else error("incomparable types", nl)
      end
    | trexp(OpExp({left, oper=NeqOp, right}, nl)) =
      let
        val {exp=_, ty=tyl} = trexp left
        val {exp=_, ty=tyr} = trexp right
      in
        if tiposIguales tyl tyr andalso not(tyl=TNil andalso tyr=TNil) andalso not(tiposIguales tyl TUnit)
          then {exp=(), ty=TInt}
          else error("incomparable types", nl)
      end
    | trexp(OpExp({left, oper, right}, nl)) =
      let
        val {exp=_, ty=tyl} = trexp left
        val {exp=_, ty=tyr} = trexp right
      in
        if tiposIguales tyl tyr then
          case oper of
            PlusOp => if tiposIguales tyl TInt then {exp=(),ty=TInt} else error("Type error", nl)
            | MinusOp => if tiposIguales tyl TInt then {exp=(),ty=TInt} else error("Type error", nl)
            | TimesOp => if tiposIguales tyl TInt then {exp=(),ty=TInt} else error("Type error", nl)
            | DivideOp => if tiposIguales tyl TInt then {exp=(),ty=TInt} else error("Type error", nl)
            | LtOp => if tiposIguales tyl TInt orelse tiposIguales tyl TString then {exp=(),ty=TInt} else error("Type error", nl)
            | LeOp => if tiposIguales tyl TInt orelse tiposIguales tyl TString then {exp=(),ty=TInt} else error("Type error", nl)
            | GtOp => if tiposIguales tyl TInt orelse tiposIguales tyl TString then {exp=(),ty=TInt} else error("Type error", nl)
            | GeOp => if tiposIguales tyl TInt orelse tiposIguales tyl TString then {exp=(),ty=TInt} else error("Type error", nl)
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
        fun verificar [] [] = ()
          | verificar (c::cs) [] = error("missing fields", nl)
          | verificar [] (c::cs) = error("spare fields", nl)
          | verificar ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
            if s<>sy then error("field error", nl)
            else if tiposIguales ty t then verificar cs ds
               else error("field's type error "^s, nl)
        val _ = verificar cs tfields
      in
        {exp=(), ty=tyr}
      end
    | trexp(SeqExp(s, nl)) =
      let  val lexti = map trexp s
        val exprs = map (fn{exp, ty} => exp) lexti
        val {exp= _, ty=tipo} = hd(rev lexti)
      in  { exp=(), ty=tipo } end
    | trexp(AssignExp({var = SimpleVar s, exp}, nl)) =
        let val _ = (case tabBusca (s, venv) of
                  NONE => error(s^": variable is not in scope", nl)
                | SOME VIntro     => error(s^": read only variable", nl)
                | SOME (Func _)   => error(s^": assigning an expression to a function", nl)
                | _               => ())
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
        if tiposIguales tytest TInt andalso tiposIguales tythen tyelse then {exp=(), ty=tythen}
        else error("Type error" ,nl)
      end
    | trexp(IfExp({test, then', else'=NONE}, nl)) =
      let val {exp=exptest,ty=tytest} = trexp test
          val {exp=expthen,ty=tythen} = trexp then'
      in
        if tiposIguales tytest TInt andalso tiposIguales tythen TUnit then {exp=(), ty=TUnit}
        else error("Type error", nl)
      end
    | trexp(WhileExp({test, body}, nl)) =
      let
        val {exp = exptest, ty = ttest} = trexp test
        val {exp = expbody, ty = tbody} = trexp body
      in
        if tiposIguales ttest TInt andalso tiposIguales tbody TUnit then {exp=(), ty=TUnit}
        else if not(tiposIguales ttest TInt) then error("type error in condition", nl)
        else error("body should be unit type", nl)
      end
    | trexp(ForExp({var, escape, lo, hi, body}, nl)) =
      let val {exp = _, ty = typHi} = trexp hi
          val {exp = _, ty = typLo} = trexp lo
          val _ = if tiposIguales typLo TInt andalso tiposIguales typHi TInt then () else error("boundaries not Int", nl)
          val venv' = fromTab venv
          val venv'' = tabInserta (var, VIntro, venv')
          val {exp = _, ty = typBody} = transExp (venv'', tenv) body
      in
          if tiposIguales typBody TUnit then {exp = (), ty = TUnit} else error("incorrect Type", nl)
      end
    | trexp(LetExp({decs, body}, _)) =
      let
        val (venv', tenv', _) = List.foldl (fn (d, (v, t, _)) => trdec(v, t) d) (venv, tenv, []) decs
        val {exp=expbody,ty=tybody} = transExp (venv', tenv') body
      in
        {exp=(), ty=tybody}
      end
    | trexp(BreakExp nl) =
      {exp=(), ty=TUnit} (*COMPLETAR*)
    | trexp(ArrayExp({typ, size, init}, nl)) =
      let val typ = (case tabBusca(typ, tenv) of
                        SOME (TArray (t, u)) => (t,u)
                        | SOME _ => error(typ^": is not an array", nl)
                        | _  => error(typ^": undefined type", nl))
          val {exp = _, ty = typInit} = trexp init
          val _ = if tiposIguales typInit (#1 typ)
                    then ()
                    else error("types do not match", nl)
          val {exp = _, ty = typSize} = trexp size
          val _ = if tiposIguales typSize TInt
                    then ()
                    else error("size isn't integer", nl)
      in {exp = (), ty = TArray typ}
      end
    and trvar(SimpleVar s, nl) =
      (case tabBusca(s, venv) of
            NONE        => error(s^": undefined variable", nl)
					| SOME VIntro => {exp = (), ty = TInt}
					| SOME (Var {ty=t}) => {exp = () , ty = t}
					| SOME _      => error(s^": is a function, not a variable", nl))
		| trvar(FieldVar(v, s), nl) =
      let val {exp = _, ty = tyv} = trvar (v, nl)
          val lflds = case tipoReal tyv of
                          TRecord (l,_)  =>  l
                          | _ => error("variable is not a record", nl)
          val (tr,nc) =  case List.find (fn (n, _, _) => n = s) lflds of
                           SOME (_,tyf, n) => (tyf,n)
                           | _ => error(s^": inexistent field in record",nl)
      in {exp = (), ty = tipoReal tr}
      end
    | trvar(SubscriptVar(v, e), nl) =
      let val {exp = _, ty = tyv} 	= trvar(v, nl)
					val {exp = _, ty = tyexp} = trexp e
					val tr = (case tipoReal tyv of
												TArray (t, _) => t
											| _             => error("variable is not an array", nl))
			in 	if tiposIguales tyexp TInt then {exp = (), ty = tr}
					else error("index is not integer", nl)
			end
    and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},pos)) =
      let val {exp = _, ty = typExp} = transExp (venv, tenv) init
          val _ = if typExp=TNil then error("variable with no explicit type is type nil", pos) else ()
          val venv' = tabRInserta (name, Var {ty=typExp}, venv)
      in (venv', tenv, []) end
    | trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},pos)) =
      let val {exp = _, ty = typExp} = transExp (venv, tenv) init
          val tt = (case tabBusca (s, tenv) of
                      SOME t => t
                      | NONE => error(s^": undefined type", pos))
          val _ = if tiposIguales tt typExp then () else error("non-matching types", pos)
          val venv' = tabRInserta (name, Var {ty = tt}, venv)
          in (venv', tenv, []) end
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
            in Func {level = (), label = tigertemp.newlabel(), formals = formal, result = resType, extern = false} end

          val fs' = List.map #1 fs
          val _ = if reps fs' then error("repeated names in batch declaration", nl) else ()
          val fEntries = List.map FDecToFEntry fs'
          val fNameEntry = zip (List.map #name fs') fEntries
          val venv' = List.foldl (fn (f,tab) => tabRInserta (#1 f, #2 f, tab)) venv fNameEntry
          val fDecFEntry = zip fs' fEntries
          fun trexpBodyNCompare ({params, body, ...}, Func {formals, result, ...}) =
            let val vars = map #name params
                val vt = zip vars formals
                val venv'' = List.foldl (fn ((v,t),e) => tabRInserta (v, Var {ty=t}, e)) venv' vt
                val {exp = _, ty = typBody} = transExp (venv'', tenv) body
            in if tiposIguales typBody result
                then ()
                else error("function body type doesn't match result type", nl)
            end
              | trexpBodyNCompare _ = error("shouldn't happen (4)", nl)
          val _ = List.map trexpBodyNCompare fDecFEntry
      in (venv', tenv, []) end
    | trdec (venv,tenv) (TypeDec []) =
      (venv, tenv, [])
    | trdec (venv, tenv) (TypeDec ts) =
      let val nl = #2 (List.hd ts)
          fun reps [] = false
          | reps ({name,...}::t) = if List.exists (fn {name = x,...} => x = name) t then true else reps t
          val ts' = map #1 ts
          val _ = if reps ts' then error("repeated names in batch declaration", nl) else ()
          val tenv' = (tigertopsort.fijaTipos ts' tenv) handle tigertopsort.Ciclo => error("Cycle", nl)
      in (venv, tenv', []) end
  in trexp end

fun transProg ex =
  let  val main =
        LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
                result=SOME "int", body=ex}, 0)]],
            body=UnitExp 0}, 0)
    val _ = transExp(tab_vars, tab_tipos) main
  in  print "good!\n" end
end
