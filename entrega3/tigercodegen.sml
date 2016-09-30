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
                         emit (OPER {assem="movl " ^ Int.toString i ^ "(`s0), `d0" ,
                                    dst = [t1], src = [t2], jump = NONE})
                 |MOVE (TEMP t1, MEM (BINOP (PLUS, TEMP t2, CONST i))) =>
                        emit (OPER {assem="movl " ^ Int.toString i ^ "(`s0), `d0" ,
                                   dst = [t1], src = [t2], jump = NONE})
                 |MOVE(MEM e1, MEM e2) => let val t = tigertemp.newtemp()
                                   in emit (OPER {assem="movl (`s0), `d0",
                                                  src = [munchExp e2],
                                                  dst = [t],
                                                  jump = NONE}) ;
                                      emit (OPER {assem = "movl `s0, (`d0)",
                                                  src = [t],
                                                  dst = [munchExp e1],
                                                  jump = NONE})
                                    end
                 |MOVE(MEM (CONST i), e) =>
                    emit (OPER {assem = "movl `s0, "^ Int.toString i,
                                src = [munchExp e],
                                dst = [],
                                jump = NONE})
                 |MOVE (e1, e2) =>  let val t = tigertemp.newtemp()
                                    in emit (OPER {assem="movl `s0, `d0",
                                                   src = [munchExp e2],
                                                   dst = [t],
                                                   jump = NONE}) ;
                                       emit (OPER {assem = "movl `s0, `d0",
                                                   src = [t],
                                                   dst = [munchExp e1],
                                                   jump = NONE})
                                     end
                 |EXP (CALL (NAME f, args)) =>
                    (saveCallerSaves() ;
                    emit (OPER {assem = "call "^f,
                                src = [],
                                dst = calldefs,
                                jump = NONE}) ;
                    munchArgs args ;
                    if (List.length args) > 0
                    then emit (OPER {assem = "addl " ^ Int.toString (List.length args) ^ ", " ^ sp,
                                    src = [],
                                    dst = [],
                                    jump = NONE})
                    else ();
                    restoreCallerSaves())
                 |EXP (CALL _) => raise Fail "Shouldn't happen (munchStm CALL _)"
                 |EXP e => emit (OPER {assem = "movl `s0 `d0",
                                      src = [munchExp e],
                                      dst = [tigertemp.newtemp()],
                                      jump = NONE})
                 |JUMP (NAME l, ls) => emit (OPER {assem = "jmp `j0",
                                                    src = [],
                                                    dst = [],
                                                    jump = SOME ls})
                 |JUMP (e, ls) => emit (OPER {assem = "jmp `s0",
                                              src = [munchExp e],
                                              dst = [],
                                              jump = SOME ls})
                 |CJUMP (reloco, e1, e2, l1, l2) =>
                    let val t1 = munchExp e1
                        val t2 = munchExp e2
                        val _  = case reloco of
                                  EQ => (emit (OPER {assem = "jnz `j0",
                                                      src = [],
                                                      dst = [],
                                                      jump = SOME [l2]}) ;
                                          emit (OPER {assem = "jz `j0",
                                                      src = [],
                                                      dst = [],
                                                      jump = SOME [l1]}))
                                  |NE => (emit (OPER {assem = "jz `j0",
                                                      src = [],
                                                      dst = [],
                                                      jump = SOME [l2]}) ;
                                          emit (OPER {assem = "jnz `j0",
                                                      src = [],
                                                      dst = [],
                                                      jump = SOME [l1]}))
                                  |LT => (emit (OPER {assem = "jnl `j0",
                                                      src = [],
                                                      dst = [],
                                                      jump = SOME [l2]}) ;
                                          emit (OPER {assem = "jl `j0",
                                                      src = [],
                                                      dst = [],
                                                      jump = SOME [l1]}))
                                  |GT => (emit (OPER {assem = "jng `j0",
                                                     src = [],
                                                     dst = [],
                                                     jump = SOME [l2]}) ;
                                         emit (OPER {assem = "jg `j0",
                                                     src = [],
                                                     dst = [],
                                                     jump = SOME [l1]}))
                                  |LE => (emit (OPER {assem = "jnle `j0",
                                                     src = [],
                                                     dst = [],
                                                     jump = SOME [l2]}) ;
                                         emit (OPER {assem = "jle `j0",
                                                     src = [],
                                                     dst = [],
                                                     jump = SOME [l1]}))
                                  |GE => (emit (OPER {assem = "jnge `j0",
                                                     src = [],
                                                     dst = [],
                                                     jump = SOME [l2]}) ;
                                         emit (OPER {assem = "jge `j0",
                                                     src = [],
                                                     dst = [],
                                                     jump = SOME [l1]}))
                                  |ULT => (emit (OPER {assem = "jnb `j0",
                                                     src = [],
                                                     dst = [],
                                                     jump = SOME [l2]}) ;
                                         emit (OPER {assem = "jb `j0",
                                                     src = [],
                                                     dst = [],
                                                     jump = SOME [l1]}))
                                  |ULE => (emit (OPER {assem = "jnbe `j0",
                                                     src = [],
                                                     dst = [],
                                                     jump = SOME [l2]}) ;
                                         emit (OPER {assem = "jbe `j0",
                                                     src = [],
                                                     dst = [],
                                                     jump = SOME [l1]}))
                                  |UGT => (emit (OPER {assem = "jna `j0",
                                                     src = [],
                                                     dst = [],
                                                     jump = SOME [l2]}) ;
                                         emit (OPER {assem = "ja `j0",
                                                     src = [],
                                                     dst = [],
                                                     jump = SOME [l1]}))
                                  |UGE => (emit (OPER {assem = "jnae `j0",
                                                     src = [],
                                                     dst = [],
                                                     jump = SOME [l2]}) ;
                                         emit (OPER {assem = "jae `j0",
                                                     src = [],
                                                     dst = [],
                                                     jump = SOME [l1]}))
                    in
                      emit (OPER {assem = "cmp `s0, `d0",
                                  src = [t1],
                                  dst = [t2],
                                  jump = NONE})
                    end
    and saveCallerSaves() =
      let fun emitedefs s = emit (OPER {assem = "pushl `s0",
                                        src = [s],
                                        dst = [],
                                        jump = NONE})
      in List.map emitedefs callersaves
      end

    and restoreCallerSaves() =
      let fun emitedefs (h::t) =
          let val _ = emit (OPER {assem = "popl `d0",
                                  src = [],
                                  dst = [h],
                                  jump = NONE})
          in emitedefs t end
      in emitedefs (List.rev callersaves)
      end

    and munchExp e =
      case e of
        MEM (BINOP (PLUS, e1, CONST i)) =>
          result (fn r => emit (OPER {assem = "movl "^ Int.toString i ^"(`s0), `d0",
                                      src = [munchExp e1],
                                      dst = [r],
                                      jump = NONE}))
      |  MEM (BINOP (PLUS, CONST i, e1)) =>
          result (fn r => emit (OPER {assem = "movl "^ Int.toString i ^"(`s0), `d0",
                                      src = [munchExp e1],
                                      dst = [r],
                                      jump = NONE}))

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
                             |TEMP t => emit (OPER {assem = "pushl " ^ t,
                                             src = [],
                                             dst = [],
                                             jump = NONE})
                             |MEM (CONST i) => emit (OPER {assem = "pushl ("^ Int.toString i ^")",
                                                      src = [],
                                                      dst = [],
                                                      jump = NONE})
                             |MEM (TEMP t) => emit (OPER {assem = "pushl ("^ t ^")",
                                                      src = [],
                                                      dst = [],
                                                      jump = NONE})
                             | _ => let val t = tigertemp.newtemp()
                                        val m = tigerassem.MOVE {assem = "movl `s0, `d0",
                                                      src = munchExp h,
                                                      dst = t}
                                    in emit m; emit (OPER {assem = "pushl "^ t,
                                                          src = [],
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
