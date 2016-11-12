structure tigercodegen =
struct

  open tigerassem
  open tigertree
  open tigerframe

  fun codegen frame stm =
    let
          val ilist = ref [] : instr list ref
          fun emit i = ilist := i :: !ilist
          fun result gen = let val t = tigertemp.newtemp()
                           in gen t ; t
                           end
          fun munchStm s =
               case s of
                  SEQ (a,b) => (munchStm a ; munchStm b) (* No deberia pasar! *)
                 |MOVE (TEMP t1, TEMP t2) =>
                     emit (tigerassem.MOVE {assem = "movl `s0, `d0",
                                            src = t2,
                                            dst = t1})
                 |MOVE (TEMP t, CONST 0) =>
                    emit (tigerassem.OPER {assem = "xorl `d0, `d0",
                                          src = [],
                                          dst = [t],
                                          jump = NONE})
                 |MOVE (TEMP t, CONST n) =>
                    emit (tigerassem.OPER {assem = "movl $" ^ Int.toString n ^", `d0",
                                           src = [],
                                           dst = [t],
                                           jump = NONE})
                 |MOVE (TEMP t1, MEM (BINOP (PLUS, CONST i, TEMP t2))) =>
                       emit (tigerassem.OPER {assem = "movl " ^ Int.toString i ^ "(`s0), `d0" ,
                                              src = [t2],
                                              dst = [t1],
                                              jump = NONE})
                 |MOVE (TEMP t1, MEM (BINOP (PLUS, TEMP t2, CONST i))) =>
                      emit (tigerassem.OPER {assem = "movl " ^ Int.toString i ^ "(`s0), `d0" ,
                                             src = [t2],
                                             dst = [t1],
                                             jump = NONE})
                 |MOVE (MEM e1, MEM e2) =>
                   let val t = tigertemp.newtemp()
                   in emit (tigerassem.OPER {assem = "movl (`s0), `d0",
                                            src = [munchExp e2],
                                            dst = [t],
                                            jump = NONE});
                      emit (tigerassem.OPER {assem = "movl `s0, (`s1)",
                                            src = [t, munchExp e1],
                                            dst = [],
                                            jump = NONE})
                    end
                |MOVE (MEM (CONST i), e) =>
                    emit (OPER {assem = "movl `s0, "^ Int.toString i,
                                src = [munchExp e],
                                dst = [],
                                jump = NONE})
                |MOVE (MEM (BINOP (PLUS, e1, CONST i)), e2) =>
                    emit (OPER {assem = "movl `s0, "^ Int.toString i^"(`s1)",
                                src = [munchExp e2, munchExp e1],
                                dst = [],
                                jump = NONE})
                |MOVE (MEM (BINOP (PLUS, CONST i, e1)), e2) =>
                  emit (OPER {assem = "movl `s0, "^ Int.toString i^"(`s1)",
                              src = [munchExp e2, munchExp e1],
                              dst = [],
                              jump = NONE})
                |MOVE (MEM e1, e2) =>
                  emit (OPER {assem = "movl `s0, (`s1)", (* Seria con () ??*)
                              src = [munchExp e2, munchExp e1],
                              dst = [],
                              jump = NONE})
                |MOVE (TEMP t, e) => emit(tigerassem.MOVE {assem = "movl `s0, `d0",
                                                          src = munchExp e,
                                                          dst = t})
                |MOVE (e1, e2) => raise Fail "Shouldn't happen (munchStm): MISSING CASES"
                |EXP (CALL (NAME f, args)) =>
                  (munchArgs (List.rev args);
                  emit (OPER {assem = "call "^f,
                              src = [],
                              dst = callersaves,
                              jump = NONE}))
                |EXP (CALL _) => raise Fail "Shouldn't happen (munchStm CALL _)"
                |EXP e => emit (tigerassem.MOVE {assem = "movl `s0 `d0",
                                                          src = munchExp e,
                                                          dst = tigertemp.newtemp()})
                |JUMP (NAME l, ls) => emit (OPER {assem = "jmp `j0",
                                                  src = [],
                                                  dst = [],
                                                  jump = SOME ls})
                |JUMP (e, ls) => emit (OPER {assem = "jmp `s0",
                                            src = [munchExp e],
                                            dst = [],
                                            jump = SOME ls})
                |CJUMP (oper, CONST a, CONST b, l1, l2) =>
                  let fun comp oper x y =
                        case oper of
                          EQ => x = y
                        | NE => x <> y
                        | LT => x < y
                        | GT => x > y
                        | LE => x <= y
                        | GE => x >= y
                        | ULT => x < y
                        | ULE => x <= y
                        | UGT => x > y
                        | UGE => x >= y
                  in emit (OPER {assem = "jmp `j0",
                                src = [],
                                dst = [],
                                jump = SOME [if (comp oper a b)
                                             then l1 else l2]})
                  end

                |CJUMP (oper, e1, e2, l1, l2) =>
                  let val t1 = munchExp e1
                      val t2 = munchExp e2
                      fun emitjmps j =  emit (OPER {assem = j^" `j0",
                                                    src = [],
                                                    dst = [],
                                                    jump = SOME [l1, l2]})
                      val _ = emit (OPER {assem = "cmpl `s1, `s0",
                                  src = [t1, t2],
                                  dst = [],
                                  jump = NONE})
                  in
                    case oper of
                       EQ => emitjmps "je"
                      |NE => emitjmps "jne"
                      |LT => emitjmps "jl"
                      |GT => emitjmps "jg"
                      |LE => emitjmps "jle"
                      |GE => emitjmps "jge"
                      |ULT => emitjmps "jb"
                      |ULE => emitjmps "jbe"
                      |UGT => emitjmps "ja"
                      |UGE => emitjmps "jae"
                  end
                |LABEL lb =>
                  emit (tigerassem.LABEL {assem = lb^":",
                                          lab = lb})

    (* and saveCallerSaves() =
      let fun emitedefs s = emit (OPER {assem = "pushl `s0",
                                        src = [s],
                                        dst = [],
                                        jump = NONE})
      in List.map emitedefs callersaves
      end

    and restoreCallerSaves() =
      let fun emitedefs [] = ()
          |   emitedefs (h::t) =
              let val _ = emit (OPER {assem = "popl `d0",
                                      src = [],
                                      dst = [h],
                                      jump = NONE})
              in emitedefs t end
      in emitedefs (List.rev callersaves)
      end
    *)

    and munchExp e =
      case e of
        MEM (BINOP (PLUS, e1, CONST i)) =>
          result (fn r => emit (tigerassem.OPER {assem = "movl "^ Int.toString i ^"(`s0), `d0",
                                                src = [munchExp e1],
                                                dst = [r],
                                                jump = NONE}))
      |MEM (BINOP (PLUS, CONST i, e1)) =>
        result (fn r => emit (tigerassem.OPER {assem = "movl "^ Int.toString i ^"(`s0), `d0",
                                              src = [munchExp e1],
                                              dst = [r],
                                              jump = NONE}))
      |MEM (CONST i) =>
        result (fn r => emit (OPER {assem = "movl "^ Int.toString i ^", `d0",
                                    src = [],
                                    dst = [r],
                                    jump = NONE}))
      |MEM e =>
        result (fn r => emit (tigerassem.OPER {assem = "movl (`s0), `d0",
                                              src = [munchExp e],
                                              dst = [r],
                                              jump = NONE}))
      |BINOP (PLUS, e1, CONST i) =>
        (*let val r = munchExp e1
        in  (emit (tigerassem.OPER {assem = "addl $" ^ Int.toString i ^ ", `d0",
                  src = [r],
                  dst = [r],
                  jump = NONE}) ; r)
        end*)
        result (fn r => (emit (OPER {assem = "movl $"^ Int.toString i ^", `d0",
                                    src = [],
                                    dst = [r],
                                    jump = NONE});
                        emit (tigerassem.OPER {assem = "addl `s0, `d0",
                                              src = [munchExp e1, r],
                                              dst = [r],
                                              jump = NONE})))
       |BINOP (PLUS, CONST i, e1) =>
         (*let val r = munchExp e1
         in  (emit (tigerassem.OPER {assem = "addl $" ^ Int.toString i ^ ", `d0",
                   src = [r],
                   dst = [r],
                   jump = NONE}) ; r)
         end*)
         result (fn r => (emit (OPER {assem = "movl $"^ Int.toString i ^", `d0",
                                      src = [],
                                      dst = [r],
                                      jump = NONE});
                          emit (tigerassem.OPER {assem = "addl `s0, `d0",
                                                src = [munchExp e1, r],
                                                dst = [r],
                                                jump = NONE})))

       |BINOP (oper, e1, e2) =>
         let fun emitOp instr =  result (fn r => (emit (tigerassem.MOVE {assem = "movl `s0, `d0",
                                                                        src = munchExp e1,
                                                                        dst = r});
                                                  emit (tigerassem.OPER {assem = instr^" `s0, `d0",
                                                                        src = [munchExp e2, r],
                                                                        dst = [r],
                                                                        jump = NONE})))
            fun emitDiv () = result (fn r => (emit (tigerassem.OPER {assem = "xorl `d0, `d0",
                                                                  src = [],
                                                                  dst = [ov],
                                                                  jump = NONE});
                                           emit (tigerassem.MOVE {assem = "movl `s0, `d0",
                                                                  src = munchExp e1,
                                                                  dst = rv});
                                           emit (tigerassem.MOVE {assem = "movl `s0, `d0",
                                                                  src = munchExp e2,
                                                                  dst = r});
                                           emit (tigerassem.OPER {assem = "idivl `s0",
                                                                  src = [r, rv, ov],
                                                                  dst = [ov, rv],
                                                                  jump = NONE});
                                           emit (tigerassem.MOVE {assem = "movl `s0, `d0",
                                                                  src = rv,
                                                                  dst = r})))
         in case oper of
            PLUS => emitOp "addl"
            |MINUS => emitOp "subl"
            |MUL => emitOp "imull"
            |DIV => emitDiv()
            |AND => emitOp "andl"
            |OR => emitOp "orl"
            |XOR => emitOp "xorl"
            | _ => raise Fail "Shouldn't happen (munchExp)"
         end

       |CONST 0 =>
        result (fn r => emit (OPER {assem = "xorl `d0, `d0",
                                   src = [],
                                   dst = [r],
                                   jump = NONE}))
       |CONST i =>
        result (fn r => emit (OPER {assem = "movl $" ^ Int.toString i ^", `d0",
                                    src = [],
                                    dst = [r],
                                    jump = NONE}))
       |NAME s =>
        result (fn r => emit (OPER {assem = "movl $" ^ s ^", `d0",
                                    src = [],
                                    dst = [r],
                                    jump = NONE}))
       |TEMP t => t
       | _ => raise Fail "Shouldn't happen (munchExp (Call))"

     and munchArgs params =
      let fun munchArgsSt [] = []
          | munchArgsSt (h::t) =
            let val _ = case h of
                              CONST i => emit (OPER {assem = "pushl $" ^ Int.toString i,
                                              src = [],
                                              dst = [],
                                              jump = NONE})
                             |NAME m => emit (OPER {assem = "pushl $" ^ m,
                                             src = [],
                                             dst = [],
                                             jump = NONE})
                             |TEMP t => emit (OPER {assem = "pushl `s0",
                                             src = [t],
                                             dst = [],
                                             jump = NONE})
                             |MEM (CONST i) => emit (OPER {assem = "pushl "^ Int.toString i,
                                                      src = [],
                                                      dst = [],
                                                      jump = NONE})
                             |MEM (TEMP t) => emit (OPER {assem = "pushl (`s0)",
                                                      src = [t],
                                                      dst = [],
                                                      jump = NONE})
                             | _ => emit (OPER {assem = "pushl `s0",
                                                src = [munchExp h],
                                                dst = [],
                                                jump = NONE})
            in
              munchArgsSt t
            end
      in
        munchArgsSt params
      end
  in
    (munchStm stm ; List.rev (!ilist))
  end
end
