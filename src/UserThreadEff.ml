open Effect
open Effect.Deep
open Printf

type _ Effect.t += 
    Fork  : (unit -> unit) -> unit t
|   Yield : unit t
|   Xchg  : int -> int t 

let fork f = perform (Fork f)
let yield () = perform Yield 
let xchg v = perform (Xchg v)

let run (main : unit -> unit) : unit =
    let exchanger : (int * (int, unit) continuation) option ref = ref None in
    let run_q : (unit -> unit) Queue.t = Queue.create () in
    let enqueue (type a) (k : (a, unit) continuation) (v : a) =
        let task () = continue k v in
        Queue.push task run_q
    in
    let dequeue () = if Queue.is_empty run_q then () else (Queue.pop run_q) ()
    in
    let rec spawn (f : unit -> unit) : unit =
        match_with f () {
            retc = dequeue;
            exnc = (fun e ->
                print_endline (Printexc.to_string e); dequeue ());
            effc = fun (type a) (eff: a t) ->
                match eff with
                |   Yield   -> 
                        Some(fun (k : (a, _) continuation) -> enqueue k (); dequeue ())
                |   Fork(f) -> 
                        Some(fun (k : (a, _) continuation) -> enqueue k (); spawn f)
                |   Xchg(n) -> 
                        Some(fun (k : (a, _) continuation) ->
                            match !exchanger with
                                None -> exchanger := Some(n,k); dequeue ()
                            |   Some(m, k2) -> exchanger := None; enqueue k m; continue k2 n
                        )
                |   _       -> None
        }
    in spawn main


let _ = run (fun _ ->
  fork (fun _ ->
    printf "[t1] Sending 0\n";
    let v = xchg 0 in
    printf "[t1] received %d\n" v);
  fork (fun _ ->
    printf "[t2] Sending 1\n";
    let v = xchg 1 in
    printf "[t2] received %d\n" v))
