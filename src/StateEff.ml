open Effect
open Effect.Deep

(* Polymorphic State handlers *)
(* we wrap the imperative and state-monad handlers in a module 
   to make them polymorphic over the type of state *)
module State (T: sig type ty end) =
    struct
        type 'a Effect.t += Get: unit -> T.ty Effect.t
        type 'a Effect.t += Put: T.ty -> unit Effect.t
        
        let get () : T.ty = perform (Get ())
        let put (s : T.ty) : unit = perform (Put s)

        let handle_state_cps (e : unit -> 'a) (state : T.ty) : 'a * T.ty = state |> match_with e () {
            retc = (fun x -> fun s -> (x, s)) ;
            exnc = raise;
            effc = fun (type a) (eff: a Effect.t) ->
                match eff with
                    Get() -> Some(fun (k: (a, 'b) continuation) -> fun (s:T.ty) -> continue k s s)
                |   Put(s)  -> Some(fun (k: (a, 'b) continuation) -> fun _ -> continue k () s)
                |   _ -> None
        }
        
        let handle_state_ref (e : unit -> 'a) (st : T.ty) : 'a * T.ty = 
            let store = ref st in
            match_with e () {
                retc = (fun x -> (x, !store));
                exnc = raise;
                effc = fun (type a) (eff: a Effect.t) ->
                    match eff with
                        Get()  -> Some(fun (k: (a, 'b) continuation) -> continue k !store)
                    |   Put(s) -> Some(fun (k: (a, 'b) continuation) -> store := s; continue k ())
                    |   _     -> None
            }
    end
    
module IntState = State(struct type ty = int end) 

open IntState

let rec fact n : unit = if (1 < n) then (put (get() * n); fact (n - 1))

let runProg n = (fst (handle_state_cps (fun () -> fact n) 1), fst (handle_state_ref (fun () -> fact n) 1))
