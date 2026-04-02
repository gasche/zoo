type t
type prepared

val create :
  unit -> t

val prepare :
  t -> prepared

val wakeup :
  prepared -> bool

type status = Wakeup_received | No_wakeup
val cancel :
  prepared -> status

val commit :
  prepared -> unit

val remote_wakeup :
  t -> unit
