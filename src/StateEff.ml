open Effect
open Effect.Deep

module State (T: sig type ty end) =
    struct
        type _ Effect.t += Get: unit -> T.ty t
        type _ Effect.t += Put: T.ty -> unit t
        
        
        let handle_state_cps e (st : T.ty) = (match_with e () {
            retc = (fun () -> fun (v:T.ty) -> v) ;
            exnc = raise;
            effc = fun (type a) (eff: a t) ->
                match eff with
                    Get() -> Some(fun (k: (a, 'b) continuation) -> fun (v:T.ty) -> continue k v v)
                |   Put(s)  -> Some(fun (k: (a, 'b) continuation) -> fun (_) -> continue k () s)
                |   _ -> None
        }) st
        
        let handle_state_ref e (st : T.ty) = 
            let store = ref st in
            match_with e () {
                retc = (fun () -> !store) ;
                exnc = raise;
                effc = fun (type a) (eff: a t) ->
                    match eff with
                        Get()  -> Some(fun (k: (a, 'b) continuation) -> continue k !store)
                    |   Put(s) -> Some(fun (k: (a, 'b) continuation) -> store := s; continue k ())
                    |   _     -> None
            }
    end
    
module IntState = State(struct type ty = int end) 

open IntState

let rec fact n : unit = if (1 < n) then (perform (Put (perform (Get ()) * n)); fact (n - 1))

let runProg n = (handle_state_cps (fun () -> fact n) 1, handle_state_ref (fun () -> fact n) 1)
