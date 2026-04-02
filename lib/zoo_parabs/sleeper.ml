type stop_flag = Mpmc_flag.t

type t =
  { mutex : Mutex.t
  ; condition : Condition.t
  ; mutable sleep : stop_flag option
  }
  (* [sleep] is protected by [mutex] *)

and prepared = stop_flag * t

let create () =
  { mutex = Mutex.create ()
  ; condition = Condition.create ()
  ; sleep = None
  }

let prepare t =
  let stop = Mpmc_flag.create () in
  Mutex.protect t.mutex @@ fun () ->
  t.sleep <- Some stop;
  (stop, t)

let wakeup (stop, t) =
  match Mpmc_flag.set stop with
  | Already_set -> false
  | First_set ->
    (*  *)
    Mutex.protect t.mutex ignore;
    (* We take the mutex to synchronize with [commit].

       After taking the mutex we know that either [commit] saw that
       the [stop] flag was already set, or it finished its own
       critical section so [Condition.wait] has been called.

       Otherwise we would risk losing the notification by calling
       [Condition.notify] below before [commit] calls
       [Condition.wait].
    *)
    (* We intentionally call Condition.notify without holding the mutex
       so that the caller of Condition.wait can take it immediately; see
       https://en.cppreference.com/w/cpp/thread/condition_variable/notify_one.html
       https://stackoverflow.com/questions/17101922/do-i-have-to-acquire-lock-before-calling-condition-variable-notify-one/17102100#17102100
     *)
    Condition.notify t.condition;
    true

type status = Wakeup_received | No_wakeup
let cancel (stop, t) =
  Mutex.protect t.mutex (fun () -> t.sleep <- None);
  match Mpmc_flag.set stop with
  | Already_set -> Wakeup_received
  | First_set -> No_wakeup

let commit (stop, t) =
  Mutex.protect t.mutex @@ fun () ->
  if not (Mpmc_flag.is_set stop) then (
    Condition.wait t.condition t.mutex;
    ignore (Mpmc_flag.set stop);
  );
  t.sleep <- None

let remote_wakeup t =
  let sleep = Mutex.protect t.mutex (fun () -> t.sleep) in
  match sleep with
  | None -> ()
  | Some stop -> ignore (wakeup (stop, t))
