open Effect
open Effect.Deep
open Printf

type 'a status = 
        Done of 'a
    |   Wait of ('a, unit) continuation list

type 'a promise = 'a status ref

type _ Effect.t += 
        Async: (unit -> 'a) -> ('a promise) Effect.t
    |   Await: 'a promise -> 'a Effect.t
    |   Yield: unit Effect.t

let async (type a) (comp : unit -> a) : a promise = perform (Async comp)
let await (type a) (prom : a promise) : a = perform (Await prom)
let yield () : unit = perform Yield 

let rec runner (type a) (main : unit -> a) : a =

    let q : (unit -> unit) Queue.t = Queue.create () in
    let next () = if not (Queue.is_empty q) then Queue.pop q () in
    let resume_task v k = Queue.add (fun () -> continue k v) q in

    let rec fulfill : 'a. 'a promise -> (unit -> 'a) -> unit = fun p e ->
        match_with e () {
            retc = (fun v -> 
                let Wait ws = !p in
                p := Done v; 
                List.iter (resume_task v) (List.rev ws);
                next ()
            );
            exnc = raise;
            effc = fun (type a) (eff : a Effect.t) ->
                match eff with
                |   Async(comp) -> Some(
                        fun (k : (a, _) continuation) -> 
                            let new_prom = ref (Wait []) in
                            Queue.add (fun () -> fulfill new_prom comp) q;
                            continue k new_prom
                    )
                |   Await(prom) -> Some(
                        fun (k: (a, _) continuation) ->
                            match !prom with
                                Done(x)  -> continue k x
                            |   Wait(ws) -> prom := Wait (k :: ws); next ()
                    )
                |   Yield -> Some(
                        fun (k: (a, _) continuation) ->
                            Queue.add (continue k) q;
                            next ()
                    )
                | _        -> None
        } in 
    let pmain = ref (Wait []) in
    fulfill pmain main; 
    let Done x = !pmain in x

let sonnet18 () : unit = 
    let prom1 = async (fun () -> printf "Shall I "; yield (); printf "compare thee ") in
    let prom2 = async (fun () -> await prom1; printf "to a ") in
    let prom3 = async (fun () -> await prom1; printf "summer's day ") in
    await prom2; await prom3

let sonnet18' () : unit = 
    let prom1 = async (fun () -> printf "Shall I "; yield (); printf "compare thee ") in
    let prom2 = async (fun () -> await prom1; printf "summer's day ") in
    await prom1;
    printf "to a ";
    await prom2

let _ = runner sonnet18'
