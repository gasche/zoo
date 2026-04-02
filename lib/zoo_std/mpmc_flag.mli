type t

val create :
  unit -> t

val is_set :
  t -> bool

type status = Already_set | First_set
val set :
  t -> status
