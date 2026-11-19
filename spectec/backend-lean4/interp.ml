(* A proof-carrying interpreter for the relations of the IL.

   For a relation `R` and a mode (which arguments are inputs), the interpreter has a function
   `interp_R_mode : inputs → List {o // R ... o ...}` that returns every output it finds
   together with a proof of `R`. Each rule becomes one function: the conclusion's input
   arguments are matched against the inputs, the premises are checked or enumerated in an
   order where their inputs are known, and the leaf proves the rule by `apply`. A rule whose
   premises fall outside this scheme is left out, so the interpreter is sound and may miss
   outputs; every left-out rule is listed in a comment with its reason. *)

open Il.Ast
open Util.Source
open Print

module SS = Set.Make (String)

exception Unsupported of string

let unsupported fmt = Printf.ksprintf (fun s -> raise (Unsupported s)) fmt

(* Free variables of an expression and of a premise. *)
let fv_exp e = SS.of_list (Il.Free.Set.elements (Il.Free.free_exp e).Il.Free.varid)
let fv_prem p = SS.of_list (Il.Free.Set.elements (Il.Free.free_prem p).Il.Free.varid)
let closed bound s = SS.subset s bound

let counter = ref 0
let fresh base = incr counter; base ^ "_" ^ string_of_int !counter

let mkvar (e : exp) x : exp = { e with it = VarE (x $ e.at) }

(* A type has classical equality if it is in `classical_eq_types` or if a type in one of its
   definitions has classical equality, since a derived instance inherits it. *)
let classical_memo : (string, bool) Hashtbl.t = Hashtbl.create 64

let rec is_classical (t : typ) = match t.it with
  | VarT (id, _) -> classical_id id
  | IterT (t', _) -> is_classical t'
  | TupT ts -> List.exists (fun (_, t) -> is_classical t) ts
  | _ -> false

and classical_id (id : id) =
  if StringSet.mem id.it !classical_eq_types then true else
  match Hashtbl.find_opt classical_memo id.it with
  | Some b -> b
  | None ->
    Hashtbl.add classical_memo id.it false;
    let b = match Il.Env.find_opt_typ !env_ref id with
      | Some (_, insts) -> List.exists (fun inst -> match inst.it with
        | InstD (_, _, dt) -> (match dt.it with
          | AliasT t -> is_classical t
          | StructT fs -> List.exists (fun (_, (t, _, _), _) -> is_classical t) fs
          | VariantT cs -> List.exists (fun (_, (t, _, _), _) -> is_classical t) cs)) insts
      | None -> false
    in
    Hashtbl.replace classical_memo id.it b;
    b

(* A proposition is decided by computable instances only if no equality or membership in it
   compares values of a type with classical equality. *)
let rec check_decidable (e : exp) =
  let walk (e : exp) = match e.it with
    | CmpE ((`EqOp | `NeOp), _, e1, e2) when is_classical e1.note
        && not (List.exists (fun (e : exp) -> match e.it with ListE [] | OptE None -> true | _ -> false) [ e1; e2 ]) ->
      unsupported "equality at %s" (Il.Print.string_of_typ e1.note)
    | MemE (e1, _) when is_classical e1.note ->
      unsupported "membership at %s" (Il.Print.string_of_typ e1.note)
    | _ -> ()
  in
  walk e;
  match e.it with
  | BinE (_, _, e1, e2) | CmpE (_, _, e1, e2) | MemE (e1, e2) | CatE (e1, e2) | CompE (e1, e2)
  | IdxE (e1, e2) -> check_decidable e1; check_decidable e2
  | UnE (_, _, e1) | LenE e1 | TheE e1 | DotE (e1, _) | ProjE (e1, _) | CvtE (e1, _, _)
  | OptE (Some e1) | LiftE e1 | CaseE (_, e1) -> check_decidable e1
  | TupE es | ListE es -> List.iter check_decidable es
  | IfE (c, e1, e2) -> check_decidable c; check_decidable e1; check_decidable e2
  | _ -> ()

(* Replace the subterms of a conclusion argument that are not Lean patterns by fresh
   variables. The result is a pattern, and each fresh variable `y` comes with the equation
   `y = e` for the subterm `e` it replaces. A variable that is bound already, or occurs twice,
   is replaced as well, with the equation to its first occurrence. *)
let rec abstract bound (e : exp) : exp * (exp * exp) list * SS.t =
  let replace () = let y = mkvar e (fresh "y") in (y, [ (y, e) ], bound) in
  match e.it with
  | VarE x when SS.mem x.it bound -> replace ()
  | VarE x -> (e, [], SS.add x.it bound)
  | BoolE _ | TextE _ | NumE (`Nat _) | OptE None -> (e, [], bound)
  | CaseE (m, e1) ->
    let (e1', ds, b) = abstract_args bound e1 in
    ({ e with it = CaseE (m, e1') }, ds, b)
  | TupE es ->
    let (es', ds, b) = abstract_list bound es in
    ({ e with it = TupE es' }, ds, b)
  | OptE (Some e1) ->
    let (e1', ds, b) = abstract bound e1 in
    ({ e with it = OptE (Some e1') }, ds, b)
  | ListE es ->
    let (es', ds, b) = abstract_list bound es in
    ({ e with it = ListE es' }, ds, b)
  | StrE fs ->
    let (es', ds, b) = abstract_list bound (List.map snd fs) in
    ({ e with it = StrE (List.map2 (fun (a, _) e' -> (a, e')) fs es') }, ds, b)
  | CatE ({ it = ListE [ e1 ]; _ } as l, e2) ->
    let (e1', ds1, b1) = abstract bound e1 in
    let (e2', ds2, b2) = abstract b1 e2 in
    ({ e with it = CatE ({ l with it = ListE [ e1' ] }, e2') }, ds1 @ ds2, b2)
  | _ -> replace ()

and abstract_args bound (e : exp) = match e.it with
  | TupE es ->
    let (es', ds, b) = abstract_list bound es in
    ({ e with it = TupE es' }, ds, b)
  | _ -> abstract bound e

and abstract_list bound es =
  List.fold_left (fun (acc, ds, b) e ->
    let (e', ds', b') = abstract b e in (acc @ [ e' ], ds @ ds', b')) ([], [], bound) es

(* A definition by clauses `f (p) = q`, where `p` and `q` are patterns over the same
   variables, has the inverse that matches `q` and returns `p`. *)
let rec is_pattern (e : exp) = match e.it with
  | VarE _ | BoolE _ | TextE _ | NumE (`Nat _) | OptE None -> true
  | CaseE (_, e1) | OptE (Some e1) -> is_pattern e1
  | TupE es | ListE es -> List.for_all is_pattern es
  | StrE fs -> List.for_all (fun (_, e) -> is_pattern e) fs
  | CatE ({ it = ListE [ e1 ]; _ }, e2) -> is_pattern e1 && is_pattern e2
  | _ -> false

let inverses : (string, string) Hashtbl.t = Hashtbl.create 16
let inverse_defs : string list ref = ref []

let inverse_of (f : id) =
  match Hashtbl.find_opt inverses f.it with
  | Some name -> Some name
  | None ->
    match Il.Env.find_opt_def !env_ref f with
    | Some ([ { it = ExpP (_, ta); _ } ], tb, clauses) when clauses <> [] ->
      let arms = List.map (fun c -> match c.it with
        | DefD (_, [ { it = ExpA p; _ } ], q, []) when is_pattern p && is_pattern q
            && SS.equal (fv_exp p) (fv_exp q) ->
          Some ("  | " ^ render_exp LHS q ^ " => some ⟨" ^ render_exp REL p ^ ", rfl⟩")
        | _ -> None) clauses in
      if List.for_all Option.is_some arms then begin
        let name = "interp_inv_" ^ f.it in
        let def =
          "def " ^ name ^ " (y : " ^ render_type REL tb ^ ") : Option {x : " ^
          render_type REL ta ^ " // " ^ render_id f.it ^ " x = y} :=\n  match y with\n" ^
          String.concat "\n" (List.map Option.get arms) ^ "\n  | _ => none" in
        Hashtbl.add inverses f.it name;
        inverse_defs := !inverse_defs @ [ def ];
        Some name
      end else None
    | _ -> None

(* Modes. *)
type mode = bool list

let mode_str (m : mode) = String.concat "" (List.map (fun b -> if b then "i" else "o") m)
let fun_name rel (m : mode) = "interp_" ^ rel ^ "_" ^ mode_str m

let worklist : (string * mode) Queue.t = Queue.create ()
let requested : (string * mode, unit) Hashtbl.t = Hashtbl.create 64

(* The (relation, mode) pairs that the functions under construction call. *)
let deps : (string * mode) list ref = ref []

let request rel (m : mode) =
  if not (List.mem (rel, m) !deps) then deps := (rel, m) :: !deps;
  if not (Hashtbl.mem requested (rel, m)) then begin
    Hashtbl.add requested (rel, m) ();
    Queue.add (rel, m) worklist
  end

(* The relation `R` at the arguments `args`, with `o` for the output position. *)
let rel_prop rel (args : string list) = parens (String.concat " " (rel :: args))

(* The result type of a mode: the outputs (at most one) with a proof of `R`. *)
let result_type rel typs (m : mode) (inputs : string list) =
  let rec args ts ms ins = match ts, ms, ins with
    | [], [], _ -> []
    | _ :: ts, true :: ms, i :: ins -> i :: args ts ms ins
    | _ :: ts, false :: ms, ins -> "o" :: args ts ms ins
    | _ -> assert false
  in
  let outs = List.filteri (fun i _ -> not (List.nth m i)) typs in
  let otyp = match outs with
    | [] -> "Unit"
    | [ t ] -> render_type REL t
    | _ -> unsupported "more than one output"
  in
  "List {o : " ^ otyp ^ " // " ^ rel_prop rel (args typs m inputs) ^ "}"

type item =
  | Eq of exp * exp            (* the bound variable `y` equals the expression `e` *)
  | Prem of prem
  | Str of string              (* a decidable proposition over bound variables *)

let hyp = ref 0
let fresh_h () = incr hyp; "h_" ^ string_of_int !hyp

(* A pattern is irrefutable if it is a variable, or a tuple or the constructor of a variant
   with one case, applied to irrefutable patterns. *)
let rec irrefutable (e : exp) = match e.it with
  | VarE _ -> true
  | TupE es -> List.for_all irrefutable es
  | StrE fs -> List.for_all (fun (_, e) -> irrefutable e) fs
  | CaseE (_, e1) ->
    (match (try Some (Il.Eval.reduce_typdef !env_ref e.note) with _ -> None) with
     | Some { it = VariantT [ _ ]; _ } -> irrefutable e1
     | _ -> false)
  | _ -> false

let fallback pats = if List.for_all irrefutable pats then "" else
  "\n | " ^ String.concat ", " (List.map (fun _ -> "_") pats) ^ " => []"

(* The values of a variant type whose cases have no arguments. *)
let enum_values (t : typ) : exp list option =
  match (try Some (Il.Eval.reduce_typdef !env_ref t) with _ -> None) with
  | Some { it = VariantT cases; _ } when cases <> [] &&
      List.for_all (fun (_, (ct, _, _), _) -> match ct.it with TupT [] -> true | _ -> false) cases ->
    Some (List.map (fun (m, (ct, _, _), _) ->
      { it = CaseE (m, { it = TupE []; note = ct; at = t.at }); note = t; at = t.at }) cases)
  | _ -> None

(* Candidates for the argument of `f` at a value `y` of its result, where the clauses of `f`
   have the form `f p = some q`. Each candidate `x` satisfies `f x = some y`; the caller checks
   that. A variable of `p` that is not in `q` ranges over the values of its type. *)
let candidates : (string, string option) Hashtbl.t = Hashtbl.create 16

let candidates_of (f : id) : string option =
  match Hashtbl.find_opt candidates f.it with
  | Some r -> r
  | None ->
    let r = match Il.Env.find_opt_def !env_ref f with
      | Some ([ { it = ExpP (_, ta); _ } ], { it = IterT (tb, Opt); _ }, clauses) ->
        (try
          let arms = List.filter_map (fun c -> match c.it with
            | DefD (_, _, { it = OptE None; _ }, []) -> None
            | DefD (quants, [ { it = ExpA p; _ } ], { it = OptE (Some q); _ }, [])
              when is_pattern p && is_pattern q && SS.subset (fv_exp q) (fv_exp p) ->
              let extra = SS.elements (SS.diff (fv_exp p) (fv_exp q)) in
              let value = List.fold_right (fun x acc ->
                let t = List.find_map (fun qu -> match qu.it with
                  | ExpP (y, t) when y.it = x -> Some t | _ -> None) quants in
                match Option.bind t enum_values with
                | Some vs -> "([" ^ String.concat ", " (List.map (render_exp REL) vs) ^
                    "] : List " ^ render_type REL (Option.get t) ^ ").flatMap fun " ^ render_id x ^ " => " ^ acc
                | None -> unsupported "candidate variable %s" x)
                extra ("[" ^ render_exp REL p ^ "]") in
              Some ("(match y with\n | " ^ render_exp LHS q ^ " => " ^ value ^ fallback [ q ] ^ ")")
            | _ -> unsupported "candidate clause") clauses in
          if arms = [] then None else begin
            let name = "interp_cand_" ^ f.it in
            inverse_defs := !inverse_defs @ [
              "def " ^ name ^ " (y : " ^ render_type REL tb ^ ") : List " ^ render_type REL ta ^ " :=\n  " ^
              String.concat " ++\n  " arms ];
            Some name
          end
        with Unsupported _ -> None)
      | _ -> None
    in
    Hashtbl.add candidates f.it r;
    r

let typed (e : exp) = parens (render_exp REL e ^ " : " ^ render_type REL e.note)

(* An equation `Option.get! (f c) = y` with `c` unbound and `y` known, in either orientation. *)
let candidate_call bound (e1 : exp) (e2 : exp) : (id * string * exp) option =
  let one a b = match a.it with
    | TheE { it = CallE (f, [ { it = ExpA { it = VarE c; _ }; _ } ]); _ }
      when not (SS.mem c.it bound) && closed bound (fv_exp b) -> Some (f, c.it, b)
    | _ -> None
  in
  match one e1 e2 with Some r -> Some r | None -> one e2 e1

(* Match the value `v` against the IL pattern `e`, then continue with `k`. *)
let rec match_value bound v (e : exp) (k : SS.t -> (exp * exp) list -> string) : string =
  let (pat, ds, bound') = abstract bound e in
  "(match " ^ v ^ " with\n | " ^ render_exp LHS pat ^ " => (" ^ k bound' ds ^ ")" ^ fallback [ pat ] ^ ")"

(* Compile the items, then the leaf. *)
and compile bound (items : item list) (leaf : SS.t -> string) : string =
  match items with
  | [] -> leaf bound
  | _ ->
    let rec pick before = function
      | [] -> unsupported "no premise is ready: %s"
                (String.concat "; " (List.map (function
                  | Eq (y, e) -> render_exp REL y ^ " = " ^ render_exp REL e
                  | Prem p -> render_prem p
                  | Str s -> s) before))
      | it :: rest -> (match step bound it (before @ rest) leaf with
        | Some code -> code
        | None -> pick (before @ [ it ]) rest)
    in
    (* A premise that only checks known values goes first, so that a recursive premise
       runs only on inputs that pass every check. *)
    let is_check = function
      | Prem { it = IfPr e; _ } -> closed bound (fv_exp e)
      | Eq (_, e) -> closed bound (fv_exp e) && not (is_classical e.note && is_pattern e && (match e.it with VarE _ -> false | _ -> true))
      | _ -> false
    in
    match List.partition is_check items with
    | c :: cs, others -> (match step bound c (cs @ others) leaf with
      | Some code -> code
      | None -> pick [] items)
    | [], _ -> pick [] items

(* One item, if it is ready. *)
and step bound it rest leaf : string option =
  let h = fresh_h () in
  match it with
  | Str s -> Some ("(if " ^ h ^ " : " ^ s ^ " then\n(" ^ compile bound rest leaf ^ ")\nelse [])")
  | Eq (y, e) ->
    let y_s = render_exp REL y in
    if closed bound (fv_exp e) && not (is_classical e.note && is_pattern e && (match e.it with VarE _ -> false | _ -> true)) then begin
      if is_classical e.note then unsupported "equality at %s" (Il.Print.string_of_typ e.note);
      check_decidable e;
      Some ("(if " ^ h ^ " : " ^ parens (y_s ^ " = " ^ render_exp REL e) ^ " then\n(" ^
        compile bound rest leaf ^ ")\nelse [])")
    end else begin match e.it with
      | CallE (f, [ { it = ExpA ({ it = VarE x; _ } as xe); _ } ]) when not (SS.mem x.it bound) ->
        (match inverse_of f with
         | Some inv ->
           Some ("(match " ^ inv ^ " " ^ y_s ^ " with\n | some ⟨" ^ render_id x.it ^ ", " ^ h ^
             "⟩ => (" ^ compile (SS.add x.it bound) rest leaf ^ ")\n | none => [])")
         | None -> None)
        |> fun r -> ignore xe; r
      | IterE ({ it = CallE (f, [ { it = ExpA { it = VarE v; _ }; _ } ]); _ },
               (((List | ListN (_, None)) as iter), [ (v', { it = VarE xs; _ }) ]))
        when v.it = v'.it && not (SS.mem xs.it bound) ->
        (match inverse_of f with
         | Some inv ->
           let bound' = SS.add xs.it bound in
           (* For `x^n` with `n` unbound, bind `n` to the length of the list. *)
           let (bind_n, bound'') = match iter with
             | ListN ({ it = VarE n; _ }, None) when not (SS.mem n.it bound) ->
               let hn = fresh_h () in
               ("(match " ^ hn ^ " : List.length " ^ render_id xs.it ^ " with\n | " ^ render_id n.it ^ " => ",
                SS.add n.it bound')
             | ListN (n, None) when not (closed bound (fv_exp n)) -> unsupported "length not determined"
             | _ -> ("(", bound')
           in
           Some ("(match interp_invMap " ^ inv ^ " " ^ y_s ^ " with\n | some ⟨" ^ render_id xs.it ^
             ", " ^ h ^ "⟩ => " ^ bind_n ^ compile bound'' rest leaf ^ ")\n | none => [])")
         | None -> None)
      | CatE (e1, e2) ->
        let a = fresh "a" and b = fresh "b" in
        let ae = mkvar e1 a and be = mkvar e2 b in
        Some ("((interp_splits " ^ y_s ^ ").flatMap fun ⟨(" ^ a ^ ", " ^ b ^ "), " ^ h ^ "⟩ => (" ^
          compile (SS.add a (SS.add b bound)) (Eq (ae, e1) :: Eq (be, e2) :: rest) leaf ^ "))")
      | _ when is_pattern e ->
        Some (match_value bound y_s e (fun bound' ds ->
          compile bound' (List.map (fun (y, e) -> Eq (y, e)) ds @ rest) leaf))
      | _ -> None
    end
  | Prem p -> step_prem bound h p rest leaf

and step_prem bound h (p : prem) rest leaf : string option =
  match p.it with
  | IfPr ({ it = CmpE (`EqOp, _, { it = VarE x; _ }, e2); _ })
    when not (SS.mem x.it bound) && closed bound (fv_exp e2) ->
    Some ("(match " ^ h ^ " : " ^ typed e2 ^ " with\n | " ^ render_id x.it ^ " => (" ^
      compile (SS.add x.it bound) rest leaf ^ "))")
  | IfPr ({ it = CmpE (`EqOp, _, e1, { it = VarE x; _ }); _ })
    when not (SS.mem x.it bound) && closed bound (fv_exp e1) ->
    Some ("(match " ^ h ^ " : " ^ typed e1 ^ " with\n | " ^ render_id x.it ^ " => (" ^
      compile (SS.add x.it bound) rest leaf ^ "))")
  | IfPr ({ it = CmpE (`EqOp, _, e1, e2); _ }) when
      (match candidate_call bound e1 e2 with Some _ -> true | None -> false) ->
    let (f, c, y) = Option.get (candidate_call bound e1 e2) in
    (match candidates_of f with
     | Some cand ->
       Some ("((" ^ cand ^ " " ^ parens (render_exp REL y) ^ ").flatMap fun " ^ render_id c ^ " => (" ^
         compile (SS.add c bound) (Prem p :: rest) leaf ^ "))")
     | None -> None)
  | IfPr ({ it = CmpE (`EqOp, _, e1, e2); _ })
    when (closed bound (fv_exp e1) && is_pattern e2 && not (closed bound (fv_exp e2)))
      || (closed bound (fv_exp e2) && is_pattern e1 && not (closed bound (fv_exp e1))) ->
    let (known, pat_e) = if closed bound (fv_exp e1) then (e1, e2) else (e2, e1) in
    let (pat, ds, bound') = abstract bound pat_e in
    Some ("(match " ^ h ^ " : " ^ typed known ^ " with\n | " ^ render_exp LHS pat ^ " => (" ^
      compile bound' (List.map (fun (y, e) -> Eq (y, e)) ds @ rest) leaf ^ ")" ^ fallback [ pat ] ^ ")")
  | IfPr ({ it = MemE ({ it = VarE x; _ }, l); _ })
    when not (SS.mem x.it bound) && closed bound (fv_exp l) ->
    Some ("((" ^ render_exp REL l ^ ").attach.flatMap fun ⟨" ^ render_id x.it ^ ", " ^ h ^ "⟩ => (" ^
      compile (SS.add x.it bound) rest leaf ^ "))")
  | IfPr e when closed bound (fv_exp e) ->
    check_decidable e;
    Some ("(if " ^ h ^ " : " ^ render_prop e ^ " then\n(" ^ compile bound rest leaf ^ ")\nelse [])")
  | IfPr _ -> None
  | RulePr (id, [], _, e) ->
    let args = transform_case_tup e in
    let m = List.map (fun a -> closed bound (fv_exp a)) args in
    let outs = List.filter (fun a -> not (closed bound (fv_exp a))) args in
    let n = List.length m in
    let mode_ok = List.for_all Fun.id (List.filteri (fun i _ -> i < n - 1) m)
      && (List.nth m (n - 1) || not (String.starts_with ~prefix:"wf_" id.it)) in
    if not mode_ok then None else begin
      request id.it m;
      let ins = List.filter (fun a -> closed bound (fv_exp a)) args in
      let call = parens (String.concat " " (fun_name id.it m :: List.map (fun a -> parens (render_exp REL a)) ins)) in
      match outs with
      | [] -> Some ("(" ^ call ^ ".flatMap fun ⟨_, " ^ h ^ "⟩ => (" ^ compile bound rest leaf ^ "))")
      | [ o ] ->
        let ov = fresh "o" in
        Some ("(" ^ call ^ ".flatMap fun ⟨" ^ ov ^ ", " ^ h ^ "⟩ => " ^
          match_value bound ov o (fun bound' ds ->
            compile bound' (List.map (fun (y, e) -> Eq (y, e)) ds @ rest) leaf) ^ ")")
      | _ -> None
    end
  | RulePr _ -> unsupported "relation with arguments"
  | IterPr (p1, ((List | Opt), [ (x, xs) ])) when closed bound (fv_exp xs)
      && closed (SS.add x.it bound) (fv_prem p1) ->
    Some ("(" ^ checker p ^ ".flatMap fun ⟨_, " ^ h ^ "⟩ => (" ^ compile bound rest leaf ^ "))")
  | IterPr _ -> None
  | LetPr (_, e1, e2) when closed bound (fv_exp e2) ->
    let (pat, ds, bound') = abstract bound e1 in
    Some ("(match " ^ h ^ " : " ^ typed e2 ^ " with\n | " ^ render_exp LHS pat ^ " => (" ^
      compile bound' (List.map (fun (y, e) -> Eq (y, e)) ds @ rest) leaf ^ ")" ^ fallback [ pat ] ^ ")")
  | LetPr _ -> None
  | NegPr _ -> unsupported "negated premise"
  | ElsePr -> unsupported "otherwise premise"

(* A decision procedure for a premise whose variables are all known, of type
   `List {_u : Unit // P}` for the proposition `P` of the premise. *)
and checker (p : prem) : string = match p.it with
  | RulePr (id, [], _, e) ->
    let args = transform_case_tup e in
    let m = List.map (fun _ -> true) args in
    request id.it m;
    parens (String.concat " " (fun_name id.it m :: List.map (fun a -> parens (render_exp REL a)) args))
  | IfPr e ->
    check_decidable e;
    let h' = fresh_h () in
    "(if " ^ h' ^ " : " ^ render_prop e ^ " then [⟨(), " ^ h' ^ "⟩] else [])"
  | IterPr (p1, ((List | Opt) as iter, [ (x, xs) ])) ->
    let typ = render_type REL (remove_iter_from_type xs.note) in
    let lst = if iter = Opt then parens ("Option.toList " ^ render_exp REL xs) else render_exp REL xs in
    "(interp_allL (fun (" ^ render_id x.it ^ " : " ^ typ ^ ") => " ^ checker p1 ^ ") " ^ lst ^ ")"
  | _ -> unsupported "iterated premise %s" (render_prem p)

let leaf_tactic rule_name =
  "by subst_vars; apply " ^ rule_name ^ " <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))"

(* The function of one rule in one mode. *)
let compile_rule rel typs (m : mode) (rule : rule) : (string * string, string) result =
  match rule.it with
  | RuleD (rule_id, quants, _, exp, prems) ->
    let fname = fun_name rel m ^ "_" ^ rule_id.it in
    try
      if List.exists (fun q -> match q.it with ExpP _ -> false | _ -> true) quants then
        unsupported "type or definition quantifier";
      let args = transform_case_tup exp in
      if List.length args <> List.length m then unsupported "arity";
      let inputs = List.mapi (fun i _ -> "a" ^ string_of_int i) args in
      let in_args = List.filteri (fun i _ -> List.nth m i) args in
      let in_names = List.filteri (fun i _ -> List.nth m i) inputs in
      let out_args = List.filteri (fun i _ -> not (List.nth m i)) args in
      let (pats, ds, bound) = abstract_list SS.empty in_args in
      let quants' = quants @ let_quants prems in
      let extra = iter_length_prems quants' exp prems @ definedness_prems quants' exp prems in
      (* A conjunction is the list of its conjuncts, so that an equation in it can bind. *)
      let rec conjuncts (p : prem) = match p.it with
        | IfPr { it = BinE (`AndOp, _, a, b); _ } ->
          conjuncts { p with it = IfPr a } @ conjuncts { p with it = IfPr b }
        | _ -> [ p ]
      in
      let items = List.map (fun (y, e) -> Eq (y, e)) ds @
        List.map (fun p -> Prem p) (List.concat_map conjuncts prems) @
        List.map (fun s -> Str s) extra in
      let leaf bound =
        if not (List.for_all (fun o -> closed bound (fv_exp o)) out_args) then
          unsupported "output not determined";
        let out = match out_args with
          | [] -> "()"
          | [ o ] -> render_exp REL o
          | _ -> unsupported "more than one output"
        in
        "[⟨" ^ out ^ ", " ^ leaf_tactic (rel ^ "." ^ render_id rule_id.it) ^ "⟩]"
      in
      let body = compile bound items leaf in
      let header =
        fname ^ " " ^
        String.concat " " (List.map2 (fun n t -> parens (n ^ " : " ^ render_type REL t))
          inputs typs |> List.filteri (fun i _ -> List.nth m i)) ^
        " : " ^ result_type rel typs m in_names ^ " :=\n"
      in
      let scrut = String.concat ", " in_names in
      let pat_s = String.concat ", " (List.map (render_exp LHS) pats) in
      let code = if pats = [] then "  " ^ body else
        "  match " ^ scrut ^ " with\n | " ^ pat_s ^ " => (" ^ body ^ ")" ^ fallback pats in
      Ok (fname, header ^ code)
    with Unsupported why -> Error (rule_id.it ^ ": " ^ why)

let prelude = {|
/- Prelude of the interpreter -/

/-- The splits of a list into a prefix and a suffix. -/
def interp_splits {α : Type} : (l : List α) → List {p : List α × List α // p.1 ++ p.2 = l}
  | [] => [⟨([], []), rfl⟩]
  | x :: xs => ⟨([], x :: xs), rfl⟩ ::
      (interp_splits xs).map fun ⟨(a, b), h⟩ => ⟨(x :: a, b), by simp [← h]⟩

/-- The inverse of `List.map f`, from an inverse of `f`. -/
def interp_invMap {α β : Type} {f : α → β} (inv : (y : β) → Option {x : α // f x = y}) :
    (l : List β) → Option {xs : List α // List.map (fun x => f x) xs = l}
  | [] => some ⟨[], rfl⟩
  | y :: ys =>
    match inv y, interp_invMap inv ys with
    | some ⟨x, hx⟩, some ⟨xs, hxs⟩ => some ⟨x :: xs, by simp [hx, ← hxs]⟩
    | _, _ => none

/-- A proof of `Forall R xs`, from proofs of `R x` for each element. -/
def interp_allL {α : Type} {R : α → Prop} (f : (x : α) → List {_u : Unit // R x}) :
    (xs : List α) → List {_u : Unit // Forall R xs}
  | [] => [⟨(), fun _ h => by cases h⟩]
  | x :: xs =>
    match f x, interp_allL f xs with
    | ⟨_, hx⟩ :: _, ⟨_, hxs⟩ :: _ => [⟨(), fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact hxs y hy⟩]
    | _, _ => []

|}

(* The strongly connected components of a graph, callees before callers. *)
let sccs (nodes : 'a list) (succ : 'a -> 'a list) : 'a list list =
  let index = Hashtbl.create 64 and low = Hashtbl.create 64 and on = Hashtbl.create 64 in
  let stack = ref [] and next = ref 0 and out = ref [] in
  let rec visit v =
    Hashtbl.replace index v !next; Hashtbl.replace low v !next; incr next;
    stack := v :: !stack; Hashtbl.replace on v ();
    List.iter (fun w ->
      if not (Hashtbl.mem index w) then begin
        visit w; Hashtbl.replace low v (min (Hashtbl.find low v) (Hashtbl.find low w))
      end else if Hashtbl.mem on w then
        Hashtbl.replace low v (min (Hashtbl.find low v) (Hashtbl.find index w))) (succ v);
    if Hashtbl.find low v = Hashtbl.find index v then begin
      let rec pop acc = match !stack with
        | w :: rest -> stack := rest; Hashtbl.remove on w;
          if w = v then w :: acc else pop (w :: acc)
        | [] -> acc
      in
      out := pop [] :: !out
    end
  in
  List.iter (fun v -> if not (Hashtbl.mem index v) then visit v) nodes;
  List.rev !out

let string_of_interp (import : string) (il : script) : string =
  ignore il;
  request "Step_pure" [ true; false ];
  request "Step" [ true; false ];
  let skipped = ref [] and count = ref 0 in
  (* For each (relation, mode): its definitions, rules first, and the pairs they call. *)
  let nodes : ((string * mode) * (string list * (string * mode) list)) list ref = ref [] in
  while not (Queue.is_empty worklist) do
    let (rel, m) = Queue.pop worklist in
    match Il.Env.find_opt_rel !env_ref (rel $ no_region) with
    | None -> skipped := !skipped @ [ rel ^ " (" ^ mode_str m ^ "): no definition" ]
    | Some (params, _, typ, rules) ->
      if params <> [] then skipped := !skipped @ [ rel ^ ": parameters" ] else begin
        let typs = transform_case_typ typ in
        let inputs = List.mapi (fun i _ -> "a" ^ string_of_int i) typs in
        let in_names = List.filteri (fun i _ -> List.nth m i) inputs in
        match (try Ok (result_type rel typs m in_names) with Unsupported w -> Error w) with
        | Error w -> skipped := !skipped @ [ rel ^ " (" ^ mode_str m ^ "): " ^ w ]
        | Ok rtyp ->
          deps := [];
          let compiled = List.map (compile_rule rel typs m) rules in
          let names = List.filter_map (function Ok (n, _) -> Some n | Error _ -> None) compiled in
          let defs = List.filter_map (function Ok (_, d) -> Some d | Error _ -> None) compiled in
          count := !count + List.length defs;
          List.iter (function
            | Ok _ -> ()
            | Error w -> skipped := !skipped @ [ rel ^ " (" ^ mode_str m ^ ") " ^ w ]) compiled;
          let header =
            fun_name rel m ^ " " ^
            String.concat " " (List.map2 (fun n t -> parens (n ^ " : " ^ render_type REL t))
              inputs typs |> List.filteri (fun i _ -> List.nth m i)) ^ " : " ^ rtyp ^ " :=\n  "
          in
          let body = match names with
            | [] -> "[]"
            | _ -> String.concat " ++\n  " (List.map (fun n ->
                String.concat " " (n :: in_names)) names)
          in
          nodes := !nodes @ [ ((rel, m), (defs @ [ header ^ body ], !deps)) ]
      end
  done;
  let succ v = match List.assoc_opt v !nodes with
    | Some (_, ds) -> List.filter (fun d -> List.mem_assoc d !nodes) ds
    | None -> [] in
  let blocks = List.map (fun comp ->
    let defs = List.concat_map (fun v -> fst (List.assoc v !nodes)) comp in
    let recursive = match comp with
      | [ v ] -> List.mem v (succ v)
      | _ -> true in
    if recursive then
      "mutual\n\n" ^ String.concat "\n\n" (List.map (fun d -> "partial def " ^ d) defs) ^ "\n\nend"
    else String.concat "\n\n" (List.map (fun d -> "def " ^ d) defs))
    (sccs (List.map fst !nodes) succ) in
  let stats = Printf.sprintf "%d rules compiled, %d left out" !count (List.length !skipped) in
  prerr_endline ("Lean 4 interpreter: " ^ stats);
  "import " ^ import ^ "\n\nset_option linter.unusedVariables false\n" ^ prelude ^
  String.concat "\n\n" !inverse_defs ^ "\n\n" ^
  String.concat "\n\n" blocks ^ "\n\n/- " ^ stats ^ ":\n" ^
  String.concat "\n" !skipped ^ "\n-/\n"
