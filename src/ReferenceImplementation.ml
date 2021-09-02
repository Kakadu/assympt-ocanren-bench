module IntMap = Map.Make(struct type t = int let compare = compare end)

let perform_occurs_check : bool ref = ref true 


(**  Terms and unification  **)

type term = Var of int | Constr of string * term list

type subst = term IntMap.t


let empty_subst : subst = IntMap.empty

let rec walk (s : subst) (t : term) : term =
  match t with
  | Var x -> (match IntMap.find_opt x s with
           | None -> t
           | Some tx -> walk s tx)
  | _     -> t

let rec occursCheck (s : subst) (x : int) (t : term) : bool =
  match walk s t with
  | Var y -> x <> y
  | Constr (_, ts) -> List.fold_left (&&) true @@ List.map (occursCheck s x) ts


let rec unify (so : subst option) (t1 : term) (t2 : term) : subst option =
  let extend (x : int) (t : term) (s : subst) : subst option =
    if !perform_occurs_check && not (occursCheck s x t)
      then None
      else Some (IntMap.add x t s)
  in match so with
   | None -> None
   | Some s -> match walk s t1, walk s t2 with
               | Var x, Var y -> if x = y then Some s else Some (IntMap.add x (Var y) s)
               | Var x, t2w -> extend x t2w s
               | t1w, Var y -> extend y t1w s
               | Constr (n1, ts1), Constr (n2, ts2) -> if n1 = n2 && List.length ts1 = List.length ts2
                                                        then List.fold_left (fun so_acc p -> unify so_acc (fst p) (snd p)) so @@ List.combine ts1 ts2
                                                        else None 

let reify (s : subst) (x : int) : term =
  let rec reify_term (t : term) : term =
    match walk s t with
    | Var _ -> t
    | Constr (n, ts) -> Constr (n, List.map reify_term ts)
  in reify_term (Var x)


(**  Streams and goals  **)

type state = subst * int

type 'a stream = Empty | Cons of 'a * 'a stream | Lazy of (unit -> 'a stream)

type goal = state -> state stream


let rec mplus (str1 : 'a stream) (str2 : 'a stream) : 'a stream =
  match str1 with
  | Empty -> str2
  | Cons (hd, tl) -> Cons (hd, mplus str2 tl)
  | Lazy l_str -> Lazy (fun () -> mplus str2 (l_str ()))


let rec bind (str : 'a stream) (f : 'a -> 'b stream) : 'b stream =
  match str with
  | Empty -> Empty
  | Cons (hd, tl) -> mplus (f hd) (bind tl f)
  | Lazy l_str -> Lazy (fun () -> bind (l_str ()) f)


let (===) (t1 : term) (t2 : term) : goal =
  fun (s, n) -> Lazy (fun () -> match unify (Some s) t1 t2 with
                                | None -> Empty
                                | Some s' -> Cons ((s', n), Empty))

let (|||) (g1 : goal) (g2 : goal) : goal =
  fun st -> Lazy (fun () -> mplus (g1 st) (g2 st))

let (&&&) (g1 : goal) (g2 : goal) : goal =
  fun st -> Lazy (fun () -> bind (g1 st) g2)

let fresh (f : term -> goal) : goal =
  fun (s, n) -> Lazy (fun () -> f (Var n) (s, n + 1))

let invoke (g : goal) : goal =
  fun st -> Lazy (fun () -> g st)


(**  Interface primitives  **)

let rec stream_to_list (str : 'a stream) : 'a list =
  match str with
  | Empty -> []
  | Cons (hd, tl) -> hd :: stream_to_list tl
  | Lazy l_str -> stream_to_list (l_str ())

let run1 (q : term -> goal) : term list =
  List.map (fun (s, _) -> reify s 0) @@ stream_to_list @@ q (Var 0) (empty_subst, 1)

let run2 (q : term -> term -> goal) : (term * term) list =
  List.map (fun (s, _) -> (reify s 0, reify s 1)) @@ stream_to_list @@ q (Var 0) (Var 1) (empty_subst, 2)


let rec print_term (t : term) : unit =
  match t with
  | Var i -> Printf.printf "x%d" i
  | Constr (name, []) -> Printf.printf "%s" name
  | Constr (name, args_hd :: args_tl) ->
      begin
      Printf.printf "%s(" name;
      print_term args_hd;
      List.iter (fun t -> Printf.printf ", "; print_term t) args_tl;
      Printf.printf ")"
      end

let run_print_gen (prefix : string) (print_ans : 'a -> unit) (ans_list : 'a list) : unit =
  Printf.printf "%s:\n" prefix;
  List.iter (fun a -> Printf.printf "  "; print_ans a; Printf.printf ";\n") ans_list

let run1_print (prefix : string) (q : term -> goal) : unit =
  run_print_gen prefix print_term (run1 q)

let run2_print (prefix : string) (q : term -> term -> goal) : unit =
  run_print_gen prefix (fun (t1, t2) -> print_term t1; Printf.printf ", "; print_term t2) (run2 q)


let run1_unreif (q : term -> goal) : state list =
  stream_to_list @@ q (Var 0) (empty_subst, 1)

let run2_unreif (q : term -> term -> goal) : state list =
  stream_to_list @@ q (Var 0) (Var 1) (empty_subst, 2)
