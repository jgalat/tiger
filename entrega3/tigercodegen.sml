structure tigercodegen =
struct

    open tigerassem
    open tigertree
    open tigerframe

    fun codegen frame stm = let
            val ilist = ref [] : instr list ref
            fun emit i = ilist := i :: !ilist
            fun result gen = let val t = tigertemp.newtemp()
                             in gen t ; t
                             end
            fun munchStm s =
                 case s of
                    SEQ (a,b) => (munchStm a ; munchStm b)
                   |MOVE (TEMP t1, MEM (BINOP (PLUS, CONST i, TEMP t2))) =>
                           emit (OPER {assem="movl " ^ Int.toString i ^ "('s0), 'd0" ,
                                      dst = [t1], src = [t2], jump = NONE})
                   |MOVE (e1, e2) => let val t = tigertemp.newtemp()
                                     in emit (OPER {assem="movl 's0, 'd0",
                                                    src = [munchExp e2],
                                                    dst = [t],
                                                    jump = NONE}) ;
                                        emit (OPER {assem = "movl 's0, 'd0",
                                                    src = [t],
                                                    dst = [munchExp e1],
                                                    jump = NONE})
                                      end
                   |MOVE(MEM e1, MEM e2) => let val t = tigertemp.newtemp()
                                     in emit (OPER {assem="movl ('s0), 'd0",
                                                    src = [munchExp e2],
                                                    dst = [t],
                                                    jump = NONE}) ;
                                        emit (OPER {assem = "movl 's0, ('d0)",
                                                    src = [t],
                                                    dst = [munchExp e1],
                                                    jump = NONE})
                                      end
                   |MOVE(MEM (CONST i), e) =>
                      emit (OPER {assem = "movl 's0, "^ Int.toString i,
                                  src = [muchExp e],
                                  dst = [],
                                  jump = NONE})
                   |EXP (CALL (NAME f, args)) =>
                    (saveCallerSaves() ;
                    emit (OPER {assem = "call "^f,
                                src = munchArgs args,
                                dst = calldefs,
                                jump = NONE}) ;
                    if (List.length args) > 0
                    then emit (OPER {assem = "addl " ^ Int.toString (List.length args) ^ ", " sp,
                                    src = [],
                                    dst = [],
                                    jump = NONE})
                    else () ;
                    restoreCallerSaves())



end
