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
                 |MOVE (TEMP t1, MEM (BINOP (PLUS, CONST i, TEMP t2))) =>
                    if t1 <> t2 then
                       emit (tigerassem.MOVE {assem = "movl " ^ Int.toString i ^ "(`s0), `d0" ,
                                  dst = t1,
                                  src = t2})
                    else
                      emit (OPER {assem = "addl $"^ Int.toString i^", `d0",
                                  src = [t1],
                                  dst = [t1],
                                  jump = NONE})
                 |MOVE (TEMP t1, MEM (BINOP (PLUS, TEMP t2, CONST i))) =>
                   if t1 <> t2 then
                      emit (tigerassem.MOVE {assem = "movl " ^ Int.toString i ^ "(`s0), `d0" ,
                                 dst = t1,
                                 src = t2})
                   else
                     emit (OPER {assem = "addl $"^ Int.toString i^", `d0",
                                 src = [t1],
                                 dst = [t1],
                                 jump = NONE})
                 |MOVE (MEM e1, MEM e2) =>
                   let val t = tigertemp.newtemp()
                   in emit (tigerassem.MOVE {assem = "movl (`s0), `d0",
                                            src = munchExp e2,
                                            dst = t});
                      emit (tigerassem.MOVE {assem = "movl `s0, (`d0)",
                                            src = t,
                                            dst = munchExp e1})
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
                  emit (OPER {assem = "movl `s0, `s1",
                              src = [munchExp e2, munchExp e1],
                              dst = [],
                              jump = NONE})
                |MOVE (TEMP t, CONST 0) =>
                  emit (OPER {assem = "xor `d0, `d0",
                              src = [],
                              dst = [t],
                              jump = NONE})
                |MOVE (TEMP t, e) => emit(tigerassem.MOVE {assem = "movl `s0, `d0",
                                                          src = munchExp e,
                                                          dst = t})
                |MOVE (e1, e2) =>  let val t = tigertemp.newtemp()
                                   in emit (tigerassem.MOVE {assem="movl `s0, `d0",
                                                             src = munchExp e2,
                                                             dst = t}) ;
                                     emit (tigerassem.MOVE {assem = "movl `s0, `d0",
                                                           src = t,
                                                           dst = munchExp e1})
                                     end
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
                 |CJUMP (oper, e1, e2, l1, l2) =>
                    let val t1 = munchExp e1
                        val t2 = munchExp e2
                        fun emitjmps jt jf = (emit (OPER {assem = jf^" `j0",
                                                          src = [],
                                                          dst = [],
                                                          jump = SOME [l2]}) ;
                                              emit (OPER {assem = jt^" `j0",
                                                          src = [],
                                                          dst = [],
                                                          jump = SOME [l1]}))
                        val _  = case oper of
                                   EQ => emitjmps "jz" "jnz"
                                  |NE => emitjmps "jnz" "jz"
                                  |LT => emitjmps "jl" "jnl"
                                  |GT => emitjmps "jg" "jng"
                                  |LE => emitjmps "jle" "jnle"
                                  |GE => emitjmps "jge" "jnge"
                                  |ULT => emitjmps "jb" "jnb"
                                  |ULE => emitjmps "jbe" "jnbe"
                                  |UGT => emitjmps "ja" "jna"
                                  |UGE => emitjmps "jae" "jnae"
                    in
                      emit (OPER {assem = "cmpl `s0, `s1",
                                  src = [t1, t2],
                                  dst = [],
                                  jump = NONE})
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
          result (fn r => emit (tigerassem.MOVE {assem = "movl "^ Int.toString i ^"(`s0), `d0",
                                                src = munchExp e1,
                                                dst = r}))
      |MEM (BINOP (PLUS, CONST i, e1)) =>
        result (fn r => emit (tigerassem.MOVE {assem = "movl "^ Int.toString i ^"(`s0), `d0",
                                              src = munchExp e1,
                                              dst = r}))
      |MEM (CONST i) =>
        result (fn r => emit (OPER {assem = "movl "^ Int.toString i ^", `d0",
                                    src = [],
                                    dst = [r],
                                    jump = NONE}))
      |MEM e =>
        result (fn r => emit (tigerassem.MOVE {assem = "movl (`s0), `d0",
                                              src = munchExp e,
                                              dst = r}))
      |BINOP (PLUS, e1, CONST i) =>
        let val r = munchExp e1
        in  (emit (tigerassem.OPER {assem = "addl $" ^ Int.toString i ^ ", `d0",
                  src = [r],
                  dst = [r],
                  jump = NONE}) ; r)
        end
        (*result (fn r => (emit (OPER {assem = "movl $"^ Int.toString i ^", `d0",
                                    src = [],
                                    dst = [r],
                                    jump = NONE});
                        emit (tigerassem.OPER {assem = "addl `s0, `d0",
                                              src = [munchExp e1, r],
                                              dst = [r],
                                              jump = NONE})))*)
       |BINOP (PLUS, CONST i, e1) =>
         let val r = munchExp e1
         in  (emit (tigerassem.OPER {assem = "addl $" ^ Int.toString i ^ ", `d0",
                   src = [r],
                   dst = [r],
                   jump = NONE}) ; r)
         end
         (*result (fn r => (emit (OPER {assem = "movl $"^ Int.toString i ^", `d0",
                                      src = [],
                                      dst = [r],
                                      jump = NONE});
                          emit (tigerassem.OPER {assem = "addl `s0, `d0",
                                                src = [munchExp e1, r],
                                                dst = [r],
                                                jump = NONE})))*)

       |BINOP (oper, e1, e2) =>
         let fun emitOp instr =  result (fn r => (emit (tigerassem.MOVE {assem = "movl `s0, `d0",
                                                                        src = munchExp e1,
                                                                        dst = r});
                                                  emit (tigerassem.OPER {assem = instr^" `s0, `d0",
                                                                        src = [munchExp e2, r],
                                                                        dst = [r],
                                                                        jump = NONE})))
         in case oper of
            PLUS => emitOp "addl"
            |MINUS => emitOp "subl"
            |MUL => emitOp "mull"
            |DIV => emitOp "divl"
            |AND => emitOp "andl"
            |OR => emitOp "orl"
            |XOR => emitOp "xorl"
            | _ => raise Fail "Shouldn't happen (munchExp)"
         end

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
                             | _ => let val t = tigertemp.newtemp()
                                        val m = tigerassem.MOVE {assem = "movl `s0, `d0",
                                                                src = munchExp h,
                                                                dst = t}
                                    in emit m; emit (OPER {assem = "pushl `s0",
                                                          src = [t],
                                                          dst = [],
                                                          jump = NONE})
                                    end
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
