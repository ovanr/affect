open Effect
open Effect.Deep

(* The lack of a proper effect system in OCaml5 means that
   we need to explicitly provide the type of elements in a generator  
   in its type signature.
   One way to do this is by having the yield operation be a function
   passed as argument.
   This is not ideal though since then we would be able to make a more optimized
   interpretation of the generator via references (see `for_gen_alt`).
 *)
type 'a gen = ('a -> unit) -> unit
let mygen : int gen = fun (yield : int -> unit) -> yield 3; yield 5


let for_gen (type a b) (gen : a gen) (handle : a -> b) : b list =
    let open struct type _ Effect.t += Yield : a -> unit Effect.t end in
    let yield (x : a) : unit = perform (Yield x) in
    match_with gen yield  {
        retc = (fun () -> []);
        exnc = raise;
        effc = fun (type r) (eff : r Effect.t) ->
            match eff with
                Yield(x) -> Some(fun (k : (r, _) continuation) -> handle x :: continue k ())
            |   _        -> None
    }


let for_gen_alt (type a b) (gen : a gen) (handle : a -> b) : b list =
    let xs = ref [] in 
    gen (fun x -> xs := handle x :: !xs);
    !xs
