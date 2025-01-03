open Effect
open Effect.Deep

module StepEff =
    struct
        type _ Effect.t += Choose: unit -> bool t
        type _ Effect.t += Yield: int -> unit t

        let handle_yield e = match_with e () {
            retc = (fun () -> []);
            exnc = raise;
            effc = fun (type a) (eff : a t) ->
                match eff with
                    Yield x -> Some(fun (k : (a, 'b) continuation) -> x :: continue k ())
                |   _        -> None
        }

        let handle_choose e = match_with e () {
            retc = (fun x -> [x]);
            exnc = raise;
            effc = fun (type a) (eff : a t) ->
                match eff with
                    Choose () -> Some(fun (k : (a, 'b) continuation) -> 
                        let open Multicont.Deep in
                        let r = promote k in
                        (resume r) true @ (resume r) false)
                |   _        -> None
        }

        let handle_choose_lazy e = match_with e () {
            retc = (fun x -> Seq.cons x Seq.empty);
            exnc = raise;
            effc = fun (type a) (eff : a t) ->
                match eff with
                    Choose () -> Some(fun (k : (a, 'b) continuation) -> 
                        let open Multicont.Deep in
                        let r = promote k in
                            fun () -> let rec go s = match s () with 
                                                        Seq.Nil -> resume r true ()
                                                      | Seq.Cons(x, s') -> Seq.Cons (x, fun () -> go s') 
                                      in go (resume r false)
                    )
                |   _        -> None
        }

    end

open StepEff

let rec step n = if n = 0 then () else
                 if n = 1 then perform (Yield 1) else
                 if perform (Choose ()) then 
                    (perform (Yield 1); step (n - 1))
                 else 
                    (perform (Yield 2); step (n - 2))
            
let m = handle_choose (fun () -> handle_yield (fun () -> step 4))
