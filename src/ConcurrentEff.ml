open Effect
open Effect.Deep

type _ Effect.t += Xchg: int -> int t

type 'a status = 
    Completed of 'a
|   Suspended of { msg: int; cont: (int, 'a status) continuation }


let step (f : unit -> 'a) () : 'a status =
    match_with f () {
        retc = (fun v -> Completed v);
        exnc = raise;
        effc = fun (type a) (eff : a t) ->
            match eff with
                Xchg(n) -> Some(fun (k : (a, _) continuation) -> Suspended({ msg = n; cont = k }))
            |   _       -> None
    }


let rec run_both (a : unit -> 'a status) (b : unit -> 'b status) : 'a * 'b =
    match a (), b () with
    |   Completed x, Completed y -> (x, y)
    |   Suspended({msg=msg1; cont=cont1}), Suspended({msg=msg2; cont=cont2}) -> 
            run_both (fun () -> continue cont1 msg2) (fun () -> continue cont2 msg1)
    |   _, _ -> failwith "Improper synchronization"


let comp1 () = perform (Xchg 0) + perform (Xchg 1)
let comp2 () = perform (Xchg 21) * perform (Xchg 21)

let run () = run_both (step comp1) (step comp2)

