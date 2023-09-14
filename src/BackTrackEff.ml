open Effect
open Effect.Deep

(* raises Continuation_already_resumed exception since it relies on multi-shot continuations *)

module BackTrackEff =
    struct
        type _ Effect.t += Decide: unit -> bool t

        let choose (type a) (x1 : a) (x2 : a) : a = if (perform (Decide ())) then x1 else x2

        let handle_decide e = try_with e () {
            effc = fun (type a) (eff : a t) ->
                match eff with
                    Decide() -> Some(fun (k : (a, 'b) continuation) -> 
                        let open Multicont.Deep in
                        let r = promote k in
                        (resume r) true || (resume r) false)
                |   _        -> None
        }
    end


let program () = 
    let open BackTrackEff in 
    55 <= (choose 5 20 + choose 35 45)

let _ = BackTrackEff.handle_decide program 
