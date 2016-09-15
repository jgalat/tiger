structure tigertips =
struct

type unique = unit ref
datatype Tipo = TUnit
  | TNil
  | TInt
  | TString
  | TArray of Tipo * unique
  | TRecord of (string * Tipo * int) list * unique
(*  | TFunc of Tipo list * Tipo *)
  | TTipo of string * Tipo option ref

fun printTipo TUnit = "TUnit"
  | printTipo TNil = "TNil"
  | printTipo TInt = "TInt"
  | printTipo TString = "TString"
  | printTipo (TArray (t,_)) = "TArray("^printTipo t^")"
  | printTipo (TRecord (l,_)) = "TRecord("^printFields l^")"
  (*| printTipo (TFunc _) = "TFunc(...)"*)
  | printTipo (TTipo(s,ref NONE)) = "TTipo("^s^",NONE!!!!)"
  | printTipo (TTipo(s,ref (SOME x))) = "TTipo("^s^","^printTipo x^")"

and printFields l = List.foldl (fn(x,y) => x^", "^y) "" (map (fn(a,b,i)=>a^":"^printTipo b^" ("^makestring(i)^")") l)
end
