open Effect
open Effect.Deep

type stack' =  EmptyS
            | ConsS of (stack -> stack) * stack'
and stack = stack' ref

type 'a status =
        Completed of 'a
    |   Waiting of ('a, stack -> stack) continuation list
and 'a promise = 'a status ref

type _ Effect.t += 
        Async: (unit -> 'a) -> ('a promise) Effect.t
    |   Await: 'a promise -> 'a Effect.t

let rec runner (type a) (main : unit -> a) : unit =

    (* let stk : stack = ref EmptyS *)
    let next (stk : stack) : (stack -> stack) option = 
            match !stk with
              EmptyS -> stk := EmptyS; None
            | ConsS(t, qv) -> stk := qv; Some t
    and add (stk : stack) (elem : stack -> stack) : unit = stk := ConsS (elem, !stk) in
    let resume_task (type a) (stk : stack) (v : a) (k : (a, stack -> stack) continuation) : unit = 
        add stk (fun stk -> continue k v stk) in 

    let rec fulfill (type a) (p : a promise) (e : unit -> a) : stack -> stack =
        match_with e () {
            retc = (fun (v : a) -> fun stk -> 
                let Waiting ws = !p in
                p := Completed v; 
                List.iter (resume_task stk v) ws; 
                match next stk with
                    None -> stk 
                |   Some t -> t stk
            );
            exnc = raise;
            effc = fun (type b) (eff : b Effect.t) ->
                match eff with
                |   Async(comp) -> Some(
                        fun (k : (b, _) continuation) -> 
                            fun stk ->
                                let new_prom = ref (Waiting []) in
                                add stk (fun () -> continue k new_prom);
                                fulfill new_prom comp stk
                    )
                (* |   Await(prom) -> Some( *)
                (*         fun (k: (a, _) continuation) -> *)
                (*             match !prom with *)
                (*                 Completed(x)  -> continue k x *)
                (*             |   Waiting(ws) -> prom := Waiting (k :: ws); next () *)
                (*     ) *)
                | _        -> None
        } in ()
    (* let p = ref (Waiting []) in *)
    (* fulfill p main; *) 
    (* let Completed x = !p in x *)
        
