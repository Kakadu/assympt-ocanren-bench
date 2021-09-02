open ReferenceImplementation


(** Evaluated relations **)

let v i = Var i
let con name args = Constr (name, args)
let cst name = Constr (name, [])


let c_O = cst "O"
let c_S t = con "S" [t]

let rec term_from_int (n : int) : term =
  if n = 0
    then c_O
    else c_S (term_from_int (n - 1))

let c_Nil = cst "Nil"
let c_Cons th tt = con "Cons" [th; tt]

let rec term_from_list (ts : term list) : term =
  match ts with
  | [] -> c_Nil
  | hd::tl -> c_Cons hd (term_from_list tl)

let prefix_term (n : int) : term =
  let rec prefix_list_acc acc n =
    if n = 0
      then acc
      else prefix_list_acc (term_from_int n :: acc) (n - 1)
  in term_from_list (prefix_list_acc [] n)


let rec le_o (x : term) (y : term) : goal =
  (x === c_O) |||
  fresh (fun x' ->
  fresh (fun y' ->
    (x === c_S x') &&&
    (y === c_S y') &&&
    invoke (le_o x' y')))

let rec plus_o (x : term) (y : term) (r : term) : goal =
  ((x === c_O) &&& (y === r)) |||
  fresh (fun x' ->
  fresh (fun r' ->
    (x === c_S x') &&&
    (r === c_S r') &&&
    invoke (plus_o x' y r')))

let rec mult_o (x : term) (y : term) (r : term) : goal =
  ((x === c_O) &&& (r === c_O)) |||
  fresh (fun x' ->
  fresh (fun r' ->
    (x === c_S x') &&&
    invoke (mult_o x' y r') &&&
    invoke (plus_o y r' r)))

let rec mult_rev_o (x : term) (y : term) (r : term) : goal =
  ((x === c_O) &&& (r === c_O)) |||
  fresh (fun x' ->
  fresh (fun r' ->
    (x === c_S x') &&&
    invoke (plus_o y r' r) &&&
    invoke (mult_rev_o x' y r')))


let rec length_o (a : term) (n : term) : goal =
  ((a === c_Nil) &&& (n === c_O)) |||
  fresh (fun h ->
  fresh (fun a' ->
  fresh (fun n' ->
    (a === c_Cons h a') &&&
    (n === c_S n') &&&
    invoke (length_o a' n'))))

let rec length_d_o (a : term) (n : term) : goal =
  ((a === c_Nil) &&& (n === c_O)) |||
  fresh (fun h ->
  fresh (fun a' ->
  fresh (fun n' ->
    (a === c_Cons h a') &&&
    invoke (length_d_o a' n') &&&
    (n === c_S n'))))

let rec incr_list_o (a : term) (r : term) : goal =
  ((a === c_Nil) &&& (r === c_Nil)) |||
  fresh (fun n ->
  fresh (fun a' ->
  fresh (fun r' ->
    (a === c_Cons n a') &&&
    (r === c_Cons (c_S n) r') &&&
    invoke (incr_list_o a' r'))))

let rec append_o (a : term) (b : term) (r : term) : goal =
  ((a === c_Nil) &&& (r === b)) |||
  fresh (fun h ->
  fresh (fun a' ->
  fresh (fun r' ->
    (a === c_Cons h a') &&&
    (r === c_Cons h r') &&&
    invoke (append_o a' b r'))))

let rec reverse_o (a : term) (r : term) : goal =
  ((a === c_Nil) &&& (r === c_Nil)) |||
  fresh (fun h ->
  fresh (fun a' ->
  fresh (fun r' ->
    (a === c_Cons h a') &&&
    invoke (reverse_o a' r') &&&
    invoke (append_o r' (c_Cons h c_Nil) r))))

let rec reverse_rev_o (a : term) (r : term) : goal =
  ((a === c_Nil) &&& (r === c_Nil)) |||
  fresh (fun h ->
  fresh (fun a' ->
  fresh (fun r' ->
    (a === c_Cons h a') &&&
    invoke (append_o r' (c_Cons h c_Nil) r) &&&
    invoke (reverse_rev_o a' r'))))



(** Evaluation primitives **)

let run_n_points (oc : out_channel) (prefix : string) (n : int) (q : int -> unit -> 'b) : unit =
  let samples = List.concat @@ List.init n (fun i ->
                      Benchmark.latency1 ~fdigits:5
                                         ~name:(Printf.sprintf "%d" (i + 1))
                                         10L
                                         (q (i + 1))
                                         ()) in
  Printf.fprintf oc "%s\n" prefix;
  List.iter (fun (name, times) -> Printf.fprintf oc "%s\t%.5f\n" name (List.hd @@ times).Benchmark.utime) samples

let run_n_points_to_file (file_name : string) (prefix : string) (n : int) (q : int -> unit -> 'b) : unit =
  let oc = open_out file_name in
  run_n_points oc prefix n q;
  close_out oc

let run_n_points_logged (oc : out_channel) (prefix : string) (n : int) (q : int -> unit -> 'b) : unit =
  let samples = List.concat @@ List.init n (fun i ->
                      Benchmark.latency1 ~fdigits:5
                                         ~name:(Printf.sprintf "%d" (i + 1))
                                         10L
                                         (q (i + 1))
                                         ()) in
  let (_, benches) = List.hd samples in
  let bench_1 = List.hd benches in
  let t_1 = bench_1.Benchmark.utime in
  let log_f i t = (log t -. log t_1) /. log (float_of_int (i + 1)) in
  Printf.fprintf oc "%s:\n" prefix;
  List.iteri (fun i (name, times) -> Printf.fprintf oc "%s\t%.5f\n" name (log_f i (List.hd @@ times).Benchmark.utime)) (List.tl samples)

let run_n_points_logged_to_file (file_name : string) (prefix : string) (n : int) (q : int -> unit -> 'b) : unit =
  let oc = open_out file_name in
  run_n_points_logged oc prefix n q;
  close_out oc



(** Evaluation queries **)

type 'b test =
  { name : string;
    param_name : string;
    prefix : string;
    query : int -> unit -> 'b;
  }

let run_test (t : 'b test) : unit =
  perform_occurs_check := true;
  run_n_points_to_file ("evaluation_results/" ^ t.name ^ "/data_points_" ^ t.name ^ "_" ^ t.param_name ^ "_with_oc.txt") ("# " ^ t.prefix) 100 t.query;
  perform_occurs_check := false;
  run_n_points_to_file ("evaluation_results/" ^ t.name ^ "/data_points_" ^ t.name ^ "_" ^ t.param_name ^ "_without_oc.txt") ("# " ^ t.prefix) 100 t.query



let leo_ground_query n m =
  let n_term = term_from_int (n * 10) in
  let m_term = term_from_int (m * 10) in
  (fun () -> run1 (fun x -> le_o n_term m_term))

let leo_ground_n_query n =
  leo_ground_query n 40

let leo_ground_n_test = {name = "leo_ground"; param_name = "n"; prefix = "le_o (n * 10) 400"; query = leo_ground_n_query}

let leo_ground_m_query m =
  leo_ground_query 40 m

let leo_ground_m_test = {name = "leo_ground"; param_name = "m"; prefix = "le_o 400 (m * 10)"; query = leo_ground_m_query}

let leo_first_query m =
  let m_term = term_from_int (m * 10) in
  (fun () -> run1 (fun x -> le_o x m_term))

let leo_first_test = {name = "leo_first"; param_name = "m"; prefix = "le_o ? (m * 10)"; query = leo_first_query}

let leo_second_query n =
  let n_term = term_from_int (n * 10) in
  (fun () -> run1 (fun y -> le_o n_term y))

let leo_second_test = {name = "leo_second"; param_name = "n"; prefix = "le_o (n * 10) ?"; query = leo_second_query}



let pluso_third_query n m =
  let n_term = term_from_int (n * 10) in
  let m_term = term_from_int (m * 500) in
  (fun () -> run1 (fun r -> plus_o n_term m_term r))

let pluso_third_n_query n =
  pluso_third_query n 10

let pluso_third_n_test = {name = "pluso_third"; param_name = "n"; prefix = "plus_o (n * 10) 5000 ?"; query = pluso_third_n_query}

let pluso_third_m_query m =
  pluso_third_query 40 m

let pluso_third_m_test = {name = "pluso_third"; param_name = "m"; prefix = "plus_o 400 (m * 500) ?"; query = pluso_third_m_query}

let pluso_second_query n k =
  let n_term = term_from_int (n * 10) in
  let k_term = term_from_int (k * 10) in
  (fun () -> run1 (fun y -> plus_o n_term y k_term))

let pluso_second_n_query n =
  pluso_second_query n 40

let pluso_second_n_test = {name = "pluso_second"; param_name = "n"; prefix = "plus_o (n * 10) ? 400"; query = pluso_second_n_query}

let pluso_second_k_query k =
  pluso_second_query 40 k

let pluso_second_k_test = {name = "pluso_second"; param_name = "k"; prefix = "plus_o 400 ? (k * 10)"; query = pluso_second_k_query}

let pluso_first_second_query k =
  let k_term = term_from_int (k * 10) in
  (fun () -> run2 (fun x y -> plus_o x y k_term))

let pluso_first_second_test = {name = "pluso_first_second"; param_name = "k"; prefix = "plus_o ? ? (k * 10)"; query = pluso_first_second_query}




let multo_third_query n m =
  let n_term = term_from_int n in
  let m_term = term_from_int m in
  (fun () -> run1 (fun r -> mult_o n_term m_term r))

let multo_third_n_query n =
  multo_third_query n 40

let multo_third_n_test = {name = "multo_third"; param_name = "n"; prefix = "mult_o n 40 ?"; query = multo_third_n_query}

let multo_third_m_query m =
  multo_third_query 2 (m * 10)

let multo_third_m_test = {name = "multo_third"; param_name = "m"; prefix = "mult_o 2 (m * 10) ?"; query = multo_third_m_query}

let multo_first_query m k =
  let m_term = term_from_int (m * 20) in
  let k_term = term_from_int (k * 10) in
  (fun () -> run1 (fun x -> mult_rev_o x m_term k_term))

let multo_first_m_query m =
  multo_first_query m 2

let multo_first_m_test = {name = "multo_first"; param_name = "m"; prefix = "mult_rev_o ? (m * 20) 20"; query = multo_first_m_query}

let multo_first_k_query k =
  multo_first_query 2 k

let multo_first_k_test = {name = "multo_first"; param_name = "k"; prefix = "mult_rev_o ? 40 (k * 10)"; query = multo_first_k_query}

let multo_first_second_query k =
  let k_term = term_from_int k in
  (fun () -> run2 (fun x y -> mult_rev_o (c_S x) (c_S y) k_term))

let multo_first_second_test = {name = "multo_first_second"; param_name = "k"; prefix = "mult_rev_o ? ? k"; query = multo_first_second_query}



let length_do_second_query l =
  let l_term = prefix_term (l * 2) in
  (fun () -> run1 (fun r -> length_d_o l_term r))

let length_do_second_test = {name = "length_do_second"; param_name = "l"; prefix = "length_d_o [1..l * 2] ?"; query = length_do_second_query}

let lengtho_second_query l =
  let l_term = prefix_term (l * 2) in
  (fun () -> run1 (fun r -> length_o l_term r))

let lengtho_second_test = {name = "lengtho_second"; param_name = "l"; prefix = "length_o [1..l * 2] ?"; query = lengtho_second_query}

let lengtho_first_query n =
  let n_term = term_from_int (n * 10) in
  (fun () -> run1 (fun a -> length_o a n_term))

let lengtho_first_test = {name = "lengtho_first"; param_name = "n"; prefix = "length_o ? (n * 10)"; query = lengtho_first_query}



let incr_listo_second_query l =
  let l_term = prefix_term (l * 2) in
  (fun () -> run1 (fun r -> incr_list_o l_term r))

let incr_listo_second_test = {name = "incr_listo_second"; param_name = "l"; prefix = "incr_list_o [1..l * 2] ?"; query = incr_listo_second_query}

let incr_listo_first_query l =
  let l_term = prefix_term (l * 2) in
  (fun () -> run1 (fun a -> incr_list_o a l_term))

let incr_listo_first_test = {name = "incr_listo_first"; param_name = "l"; prefix = "incr_list_o ? [1..l * 2]"; query = incr_listo_first_query}



let appendo_third_query l1 l2 =
  let l1_term = prefix_term (l1 * 2) in
  let l2_term = prefix_term (l2 * 10) in
  (fun () -> run1 (fun r -> append_o l1_term l2_term r))

let appendo_third_l1_query l1 =
  appendo_third_query l1 40

let appendo_third_l1_test = {name = "appendo_third"; param_name = "l1"; prefix = "append_o [1..l * 2] [1..80] ?"; query = appendo_third_l1_query}

let appendo_third_l2_query l2 =
  appendo_third_query 5 l2

let appendo_third_l2_test = {name = "appendo_third"; param_name = "l2"; prefix = "append_o [1..10] [1..l * 10] ?"; query = appendo_third_l2_query}

let appendo_first_second_query l =
  let l_term = prefix_term l in
  (fun () -> run2 (fun a b -> append_o a b l_term))

let appendo_first_second_test = {name = "appendo_first_second"; param_name = "l"; prefix = "append_o ? ? [1..l]"; query = appendo_first_second_query}



let reverseo_second_query l =
  let l_term = prefix_term l in
  (fun () -> run1 (fun r -> reverse_o l_term r))

let reverseo_second_test = {name = "reverseo_second"; param_name = "l"; prefix = "reverse_o [1..l] ?"; query = reverseo_second_query}

let reverseo_first_query l =
  let l_term = prefix_term l in
  (fun () -> run1 (fun a -> reverse_rev_o a l_term))

let reverseo_first_test = {name = "reverseo_first"; param_name = "l"; prefix = "reverse_o ? [1..l]"; query = reverseo_first_query}



(** MAIN **)

let _ =
  (**) run_test leo_ground_n_test; (**)
  (**) run_test leo_ground_m_test; (**)
  (**) run_test leo_first_test; (**)
  (** ) run_test leo_second_test; ( **)
  (** ) run_test pluso_third_n_test; ( **)
  (** ) run_test pluso_third_m_test; ( **)
  (** ) run_test pluso_second_n_test; ( **)
  (** ) run_test pluso_second_k_test; ( **)
  (** ) run_test pluso_first_second_test; ( **)
  (** ) run_test multo_third_n_test; ( **)
  (** ) run_test multo_third_m_test; ( **)
  (** ) run_test multo_first_m_test; ( **)
  (** ) run_test multo_first_k_test; ( **)
  (** ) run_test multo_first_second_test; ( **)
  (** ) run_test length_do_second_test; ( **)
  (** ) run_test lengtho_second_test; ( **)
  (** ) run_test lengtho_first_test; ( **)
  (** ) run_test incr_listo_second_test; ( **)
  (** ) run_test incr_listo_first_test; ( **)
  (** ) run_test appendo_third_l1_test; ( **)
  (** ) run_test appendo_third_l2_test; ( **)
  (** ) run_test appendo_first_second_test; ( **)
  (** ) run_test reverseo_second_test; ( **)
  (** ) run_test reverseo_first_test; ( **)
