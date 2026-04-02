type t

val create :
  unit -> t

val push :
  t -> Sleeper.prepared -> unit

val wakeup_one :
  t -> unit

val wakeup_all :
  t -> unit
