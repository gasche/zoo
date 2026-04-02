type t =
  bool Atomic.t

let create () =
  Atomic.make false

let is_set =
  Atomic.get

type status = Already_set | First_set
let set t =
  if Atomic.exchange t true
  then Already_set
  else First_set
