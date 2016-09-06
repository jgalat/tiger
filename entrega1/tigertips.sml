structure tigertips =
struct

type unique = unit ref
datatype Tipo = TUnit
  | TNil
  | TInt
  | TString
  | TArray of Tipo * unique
  | TRecord of (string * Tipo * int) list * unique
  | TTipo of string * Tipo option ref
end
