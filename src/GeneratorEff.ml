(* This file is largely based on:
    https://github.com/ocaml-multicore/ocaml-effects-tutorial/blob/master/sources/solved/generator.ml
   with some adjustments made:
    ∙ an iterator does not take a container but instead it only
      takes a function to perform on each element.
      Thus iterators embed containers in them and don't take it as argument
    ∙ The generate solution uses the handler's return branch instead of
      defining a recursive reference to avoid the last continuation from being called more than once
 *)
type 'elt iterator = ('elt -> unit) -> unit

type 'elt generator = unit -> 'elt option

(* Reference Store that returns the old value of the reference *)
let (<!-) r y = let x = !r in r := y; x

let generate_shallow (type elt) (i : elt iterator) : elt generator =
    let open Effect in
    let open Effect.Shallow in
    let open struct
        type _ Effect.t +=
            Yield : elt -> unit Effect.t
    end in 
    let yield x = perform (Yield x) in
    let refc = ref (fiber (fun () -> i yield)) in
    fun () ->
        let comp = refc <!- (fiber (fun () -> ())) in
        continue_with comp () {
            retc = (fun () -> None);
            exnc = raise;
            effc = fun (type a) (eff : a Effect.t) ->
                match eff with
                    Yield(x) -> Some(fun (k: (a, _) continuation) -> 
                        refc := k;
                        Some(x)
                    )
                |   _ -> None
        }

let generate_deep (type elem) (i : elem iterator) : elem generator =
    let open Effect in
    let open Effect.Deep in
    let open struct
        type _ Effect.t +=
            Yield : elem -> unit Effect.t
    end in 
    let yield x = perform (Yield x) in
    let rec cont = ref (fun () ->
        match_with i yield {
            retc = (fun () -> cont := (fun () -> None); None);
            exnc = raise;
            effc = fun (type a) (eff : a Effect.t) ->
                match eff with
                    Yield(x : elem) -> Some(fun (k: (a, _) continuation) -> 
                        cont := continue k;
                        Some(x)
                    )
                |   _ -> None
        }) in
    fun () -> !cont ()


let iterate (type elt) (g : elt generator) : elt iterator =
    fun f -> 
        let rec run_gen () = match g () with 
                                None -> ()
                            |   Some(x) -> f x; run_gen () in
        run_gen ()
            

(***********************)
(* Traversal generator *)
(***********************)

let list_iter (type a) (xs : a list) : a iterator = 
    fun (f : a -> unit) : unit ->
        let rec go xs = 
            match xs with
                x :: xxs -> f x; go xxs
            | [] -> ()
        in go xs

let list_gen (type a) (xs : a list) : a generator =
    let rxs = ref xs in
    fun () ->
        match !rxs with
          x :: xxs -> rxs := xxs ; Some(x)
        | [] -> None


let gen_list : 'a list -> 'a generator = fun xs -> generate_deep (list_iter xs)
let gl : int generator = gen_list [1;2;3]
;;

assert (Some 1 = gl ());;
assert (Some 2 = gl ());;
assert (Some 3 = gl ());;
assert (None = gl ());;
assert (None = gl ());;

let gen_array : 'a array -> 'a generator = fun arr -> generate_deep (Fun.flip Array.iter arr)
let ga : float generator = gen_array [| 1.0; 2.0; 3.0 |]
;;


assert (Some 1.0 = ga ());;
assert (Some 2.0 = ga ());;
assert (Some 3.0 = ga ());;
assert (None = ga ());;
assert (None = ga ());;

(***********)
(* Streams *)
(***********)

(* Iterator over nats. Dummy () container. *)
let rec nats : int (* init *) -> int iterator =
    fun v f ->
    f v; nats (v+1) f

(* Infinite stream *)
type 'a stream = unit -> 'a

(* Convert generator to an infinite stream *)
let inf : 'a generator -> 'a stream  =
    fun g () ->
    match g () with
    | Some n -> n
    | _ -> assert false

(* Nat stream *)
let gen_nats : int stream = inf (generate_deep (nats 0))
;;

assert (0 = gen_nats ());;
assert (1 = gen_nats ());;
assert (2 = gen_nats ());;
assert (3 = gen_nats ());;

(* filter stream *)
let rec filter : 'a stream -> ('a -> bool) -> 'a stream =
    fun g p () ->
    let v = g () in
    if p v then v
    else filter g p ()

(* map stream *)
let rec map : 'a stream -> ('a -> 'b) -> 'b stream =
    fun g f () -> f (g ())

(* Even stream *)
let gen_even : int stream =
    let nat_stream = inf (generate_deep (nats 0)) in
    filter nat_stream (fun n -> n mod 2 = 0)
;;

assert (0 = gen_even ());;
assert (2 = gen_even ());;
assert (4 = gen_even ());;
assert (6 = gen_even ());;

(* Odd stream *)
let gen_odd : int stream =
    let nat_stream = inf (generate_deep (nats 1)) in
    filter nat_stream (fun n -> n mod 2 == 1)
;;


assert (1 = gen_odd ());;
assert (3 = gen_odd ());;
assert (5 = gen_odd ());;
assert (7 = gen_odd ());;

(* Primes using sieve of Eratosthenes *)
let gen_primes =
    let s = inf (generate_deep (nats 2)) in
    let rs = ref s in
    fun () ->
    let s = !rs in
    let prime = s () in
    rs := filter s (fun n -> n mod prime != 0);
    prime
;;

assert ( 2 = gen_primes ());;
assert ( 3 = gen_primes ());;
assert ( 5 = gen_primes ());;
assert ( 7 = gen_primes ());;
assert (11 = gen_primes ());;
assert (13 = gen_primes ());;
assert (17 = gen_primes ());;
assert (19 = gen_primes ());;
assert (23 = gen_primes ());;
assert (29 = gen_primes ());;
assert (31 = gen_primes ());;
