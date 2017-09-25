module UI = Algorithms.UnIn(Incl.StateSet)(Incl.StateStateSetF(Incl.StateSet))

let is_universal a = UI.is_universal a
let is_included a1 a2 = UI.is_language_included ~blabla:false a1 a2
let are_equiv a1 a2 = is_included a1 a2 && is_included a2 a1 
let bisimin a = Bisimin.bisimin a


