open Effect
open Effect.Deep

let invert (type a) ~(iter: (a -> unit) -> unit) : a Seq.t = 
    let open struct type _ Effect.t += Yield: a -> unit t end
    in fun () -> match_with iter (fun x -> perform (Yield x)) {
        retc = (fun () -> Seq.Nil);
        exnc = raise ;
        effc = fun (type b) (eff : b t) -> 
            match eff with
                Yield v -> Some(fun (k : (b, _) continuation) -> 
                    Seq.Cons (v, fun () -> continue k ())
                )
            |   _ -> None
    }
