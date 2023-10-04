open Effect
open Effect.Deep
open Printf

type queue = Queue of (queue -> queue) list ref

type promiseId = int

type status = 
        Done 
    |   Wait of (queue -> queue) list

type promise = status ref

type 'a cPromise = promiseId * 'a option ref 

type _ Effect.t += 
        Async: (unit -> unit) -> promiseId Effect.t
    |   Await: promiseId -> promiseId Effect.t

let async (comp : unit -> unit) : promiseId = perform (Async comp)
let await (prom : promiseId) : unit = perform (Await prom); ()
let yield () : unit = await (async (fun () -> ())); ()

let async' (type a) (comp : unit -> a) : a cPromise =
    let res = ref None in
    (async (fun () -> res := Some(comp ())), res)

let await' (type a) (prom : a cPromise) : a = 
    match prom with
        (pid, res) -> await pid;
                      match !res with
                        None -> assert false
                      | Some(v) -> v

let rec runner (type a) (main : unit -> unit) : unit =

    let q : queue = Queue (ref []) in
    let promises : promise list ref = ref [] in
    let next () : (queue -> queue) option = 
        let Queue q' = q in
        match !q' with
            [] -> q' := []; None
        | (j :: js) -> q' := js; Some(j) in
    let resume_task k = () in
    let modifyPromise : promiseId -> (promise -> unit) -> unit = fun pid f -> () in
    let isPromiseDone : promiseId -> bool option = fun pid -> Some true in
    let nextPromId () = 0 in

    let rec fulfill : promiseId -> (unit -> unit) -> queue -> queue = fun p e q ->
        match_with e () {
            retc = (fun v q -> 
                modifyPromise p (fun st ->
                        match !st with
                            Done -> ()
                        |   Wait(ws) ->
                                st := Done; 
                                List.iter resume_task (List.rev ws));
                match next () with 
                    None -> q
                |   Some(job) -> job q
            );
            exnc = raise;
            effc = fun (type a) (eff : a Effect.t) ->
                match eff with
                |   Async(comp) -> Some(
                        fun (k : (a, _) continuation) -> 
                            let new_prom = nextPromId () in
                            Queue.add (fun () -> fulfill new_prom comp) q;
                            continue k new_prom
                    )
                |   Await(promId) -> Some(
                        fun (k: (a, _) continuation) ->
                            modifyPromise promId (fun st ->
                                    match !st with
                                        Done  -> () 
                                    |   Wait(ws) -> st := Wait ((fun () -> continue k promId) :: ws));
                            match isPromiseDone promId with
                                Some(true) -> continue k promId 
                            |   _          -> next ())
                | _        -> None
        } in 
    let pmain = nextPromId () in
    fulfill pmain main 

let sonnet18 () : unit = 
    let prom1 = async (fun () -> printf "Shall I "; yield (); printf "compare thee ") in
    let prom2 = async (fun () -> await prom1; printf "to a ") in
    let prom3 = async (fun () -> await prom1; printf "summer's day ") in
    await prom2; await prom3; ()

let _ = runner sonnet18