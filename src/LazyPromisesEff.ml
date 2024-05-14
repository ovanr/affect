open Effect
open Effect.Deep

type 'a status = 
        Completed of 'a
    |   NotStarted of (unit -> 'a)
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
                match !p with
                |   Waiting(ws)   -> 
                        p := Completed v; 
                        List.iter (resume_task v) ws;
                        next ()
                |   _ -> assert false
            );
            exnc = raise;
            effc = fun (type a) (eff : a Effect.t) ->
                match eff with
                |   Async(comp) -> Some(
                        fun (k : (a, _) continuation) -> 
                            let new_prom = ref (NotStarted comp) in
                            continue k new_prom
                    )
                |   Await(prom) -> Some(
                        fun (k: (a, _) continuation) ->
                            match !prom with
                                Completed(x)  -> continue k x
                            |   NotStarted(comp) -> 
                                prom := Waiting [k]; 
                                Queue.add (fun () -> fulfill prom comp) q;
                                next ()
                            |   Waiting(ws) -> 
                                    prom := Waiting (k :: ws); 
                                    next ()
                    )
                | _        -> None
        } in
    let pmain = ref (Waiting []) in
    fulfill pmain main; 
    let Completed x = !pmain in x

let deadlock () = 
    let r : unit promise option ref = ref None in
    let rec f () : unit = 
        match !r with
            None -> let wt = perform (Async (fun () -> ())) in perform (Await wt); f ()
        |   Some(p) -> perform (Await p) in

    let prom = perform (Async f) in r := Some(prom); f () 
