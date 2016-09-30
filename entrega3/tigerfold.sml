structure tigerfold :> tigerfold=
struct

  open tigertree

  fun constFolding s =
    let val change = ref false
        fun c() = (change := true)
        fun constFoldingStm stmts =
          (case stmts of
            MOVE (e1,e2) => MOVE (constFoldingExp e1, constFoldingExp e2)
          | EXP e => EXP (constFoldingExp e)
          | JUMP (e, l) => JUMP (constFoldingExp e, l)
          | CJUMP (r,e1,e2,l1,l2) => CJUMP (r, constFoldingExp e1, constFoldingExp e2, l1, l2)
          | _ => stmts)
        and constFoldingExp expr =
          (case expr of
            BINOP (PLUS, CONST i1, CONST i2) => (* 1 *)
              (c(); CONST (i1 + i2))
          | BINOP (PLUS, e, CONST i) => (* 2 *)
              (c(); BINOP (PLUS, CONST i, constFoldingExp e))
          | BINOP (MUL, CONST i1, CONST i2) => (* 3 *)
              (c(); CONST (i1 * i2))
          | BINOP (MUL, e, CONST i) => (* 4 *)
              (c(); BINOP (MUL, CONST i, constFoldingExp e))
          | BINOP (MINUS, CONST i1, CONST i2) => (* 5 *)
              (c(); CONST (i1 - i2))
          | BINOP (MINUS, e, CONST i) => (* 6 *)
              (c(); BINOP (PLUS, CONST (~i), constFoldingExp e))
          | BINOP (PLUS, e1, BINOP (PLUS, e2, e3)) => (* 7 *)
              (c(); BINOP (PLUS, BINOP (PLUS, constFoldingExp e1, constFoldingExp e2), constFoldingExp e3))
          | BINOP (MUL, e1, BINOP (MUL, e2, e3)) => (* 8 *)
              (c(); BINOP (MUL, BINOP (MUL, constFoldingExp e1, constFoldingExp e2), constFoldingExp e3))
          | BINOP (PLUS, BINOP (PLUS, CONST i1, e), CONST i2) => (* 9 *)
              (c(); BINOP (PLUS, CONST (i1 + i2), constFoldingExp e))
          | BINOP (MUL, BINOP (MUL, CONST i1, e), CONST i2) => (* 10 *)
              (c(); BINOP (MUL, CONST (i1 * i2), constFoldingExp e))
          | BINOP (MUL, BINOP (PLUS, CONST i1, e), CONST i2) => (* 11 *)
              (c(); BINOP (PLUS, CONST (i1 * i2), BINOP (MUL, CONST i2, constFoldingExp e)))
          | BINOP (MUL, CONST i1, BINOP (PLUS, CONST i2, e)) => (* 12 *)
              (c(); BINOP (PLUS, CONST (i1 * i2), BINOP (MUL, CONST i1, constFoldingExp e)))
          | BINOP (MUL, BINOP (PLUS, e1, e2), CONST i) => (* 13 *)
              (c(); BINOP (PLUS, BINOP (MUL, CONST i, constFoldingExp e1), BINOP (MUL, CONST i, constFoldingExp e2)))
          | BINOP (MUL, CONST i, BINOP (PLUS, e1, e2)) => (* 14 *)
              (c(); BINOP (PLUS, BINOP (MUL, CONST i, constFoldingExp e1), BINOP (MUL, CONST i, constFoldingExp e2)))
          | BINOP (MUL, BINOP (MINUS, e1, e2), CONST i) => (* 15 *)
              (c(); BINOP (MINUS, BINOP (MUL, CONST i, constFoldingExp e1), BINOP (MUL, CONST i, constFoldingExp e2)))
          | BINOP (MUL, CONST i, BINOP (MINUS, e1, e2)) => (* 16 *)
              (c(); BINOP (MINUS, BINOP (MUL, CONST i, constFoldingExp e1), BINOP (MUL, CONST i, constFoldingExp e2)))
          | BINOP (MUL, BINOP (PLUS, e1, e2), e3) => (* 17 *)
              (c(); BINOP (PLUS, BINOP (MUL, constFoldingExp e1, constFoldingExp e3), BINOP (MUL, constFoldingExp e2, constFoldingExp e3)))
          | BINOP (MUL, e1, BINOP (PLUS, e2, e3)) => (* 18 *)
              (c(); BINOP (PLUS, BINOP (MUL, constFoldingExp e1, constFoldingExp e2), BINOP (MUL, constFoldingExp e1, constFoldingExp e3)))
          | BINOP (MUL, BINOP (MINUS, e1, e2), e3) => (* 19 *)
              (c(); BINOP (MINUS, BINOP (MUL, constFoldingExp e1, constFoldingExp e3), BINOP (MUL, constFoldingExp e2, constFoldingExp e3)))
          | BINOP (MUL, e1, BINOP (MINUS, e2, e3)) => (* 20 *)
              (c(); BINOP (MINUS, BINOP (MUL, constFoldingExp e1, constFoldingExp e2), BINOP (MUL, constFoldingExp e1, constFoldingExp e3)))
          | BINOP (oper, e1, e2) =>
              BINOP (oper, constFoldingExp e1, constFoldingExp e2)
          | MEM e =>
              MEM (constFoldingExp e)
          | CALL (e1, e2) =>
              CALL (constFoldingExp e1, constFolding e2)
          | _ => expr)
    in
      (*
        if (!change)
        then (change := false; constFolding (List.map constFoldingStm s))
        else List.map constFoldingStm s
      *)
        s
    end
end
