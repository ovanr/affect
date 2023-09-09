open Effect
open Effect.Deep
open Printf

type 'a status = 
        Completed of 'a
    |   Waiting of ('a, unit) continuation list

type 'a promise = 'a status ref

type _ Effect.t += 
        Async: (unit -> 'a) -> ('a promise) Effect.t
    |   Await: 'a promise -> 'a Effect.t

let async (type a) (comp : unit -> a) : a promise = perform (Async comp)
let await (type a) (prom : a promise) : a = perform (Await prom)
let yield () : unit = await (async (fun () -> ()))

let rec runner (type a) (main : unit -> a) : a =

    let q : (unit -> unit) Queue.t = Queue.create () in
    let next () = if not (Queue.is_empty q) then Queue.pop q ()
    and resume_task v k = Queue.add (fun () -> continue k v) q in

    let rec fulfill : 'a. 'a promise -> (unit -> 'a) -> unit = fun p e ->
        match_with e () {
            retc = (fun v -> 
                let Waiting ws = !p in
                p := Completed v; 
                List.iter (resume_task v) (List.rev ws); 
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

let sonnet18 () : unit = 
    let prom1 = async (fun () -> printf "Shall I "; yield (); printf "compare thee ") in 
    let prom2 = async (fun () -> await prom1; printf "to a ") in
    let prom3 = async (fun () -> await prom1; printf "summer's day ") in
    await prom2; await prom3
