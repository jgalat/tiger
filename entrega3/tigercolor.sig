signature tigercolor =
sig

  type allocation = (tigertemp.temp, tigerframe.register) Splaymap.dict

  val alloc : tigerassem.instr list * tigerframe.frame -> allocation * tigerassem.instr list


end
