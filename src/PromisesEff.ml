open Effect
open Effect.Deep

type 'a status = 
        Completed of 'a
    |   Waiting of ('a, unit) continuation list

type 'a promise = 'a status ref

type _ Effect.t += 
        Async: (unit -> 'a) -> ('a promise) Effect.t
    |   Await: 'a promise -> 'a Effect.t

let rec runner (type a) (main : unit -> a) : a =

    let q : (unit -> unit) Queue.t = Queue.create () in
    let next () = if not (Queue.is_empty q) then Queue.pop q ()
    and resume_task v k = Queue.add (fun () -> continue k v) q in

    let rec fulfill : 'a. 'a promise -> (unit -> 'a) -> unit = fun p e ->
        match_with e () {
            retc = (fun v -> 
                let Waiting ws = !p in
                p := Completed v; 
                List.iter (resume_task v) ws; 
                next ()
            );
            exnc = raise;
            effc = fun (type a) (eff : a Effect.t) ->
                match eff with
                |   Async(comp) -> Some(
                        fun (k : (a, _) continuation) -> 
                            let new_prom = ref (Waiting []) in
                            Queue.add (fun () -> continue k new_prom) q;
                            fulfill new_prom comp
                    )
                |   Await(prom) -> Some(
                        fun (k: (a, _) continuation) ->
                            match !prom with
                                Completed(x)  -> continue k x
                            |   Waiting(ws) -> prom := Waiting (k :: ws); next ()
                    )
                | _        -> None
        } in 
    let p = ref (Waiting []) in
    fulfill p main; 
    let Completed x = !p in x
        
