open Il.Ast
open Util.Source

module StringSet = Set.Make(String)

let iter_prem_rels_list = ["Forall"; "Forall₂"; "Forall₃"]
let iter_exp_lst_funcs = ["List.map"; "List.zipWith"; "list_map3"]
let iter_exp_opt_funcs = ["Option.map"; "option_zipWith"; "option_map3"]
let error at msg = Util.Error.error at "Lean4 translation" msg 

(* List of declaration ids that are hand-coded in the preamble *)
let builtins = [ "disjoint_"; "setminus1_"; "setminus_" ]

let rec list_split (f : 'a -> bool) = function 
  | [] -> ([], [])
  | x :: xs when f x -> let x_true, x_false = list_split f xs in
    (x :: x_true, x_false)
  | xs -> ([], xs)

type exptype =
  | LHS
  | RHS
  | REL

let var_prefix = "var_"

let remove_iter_from_type t =
  match t.it with
  | IterT (t', _) -> t'
  | _ -> t
let empty_name s = match s with
  | "" -> "NO_NAME"
  | _ -> s

let string_of_list_prefix prefix delim str_func ls = 
  match ls with
  | [] -> ""
  | _ -> prefix ^ String.concat delim (List.map str_func ls)

let string_of_list_suffix suffix delim str_func ls =
  match ls with
  | [] -> ""
  | _ -> String.concat delim (List.map str_func ls) ^ suffix

let string_of_list prefix suffix delim str_func ls =
  match ls with
  | [] -> ""
  | _ -> prefix ^ String.concat delim (List.map str_func ls) ^ suffix

let square_parens s = "[" ^ s ^ "]"
let parens s = "(" ^ s ^ ")"
let curly_parens s = "{" ^ s ^ "}"
let comment_parens s = "/- " ^ s ^ " -/"

let family_type_suffix = "entry"

let env_ref = ref Il.Env.empty

let is_record_typ inst = 
  match inst.it with
  | InstD (_, _, {it = StructT _; _}) -> true
  | _ -> false

let is_variant_typ inst = 
  match inst.it with
  | InstD (_, _, {it = VariantT _; _}) -> true
  | _ -> false

let is_alias_typ inst = 
  match inst.it with
  | InstD (_, _, {it = AliasT _; _}) -> true
  | _ -> false

let is_alias_typ_def def = 
  match def.it with
  | TypD(_ , _, [{it = InstD (_, _, {it = AliasT _; _}); _}]) -> true
  | _ -> false

let check_trivial_append env typ = 
  match typ.it with
  | IterT (_t, _) -> true (* check_trivial_append env t *) (* JB: Why not trivial? *)
  | VarT (id, _) -> 
    begin match (Il.Env.find_opt_typ env id) with
    | Some (_, [inst]) when is_record_typ inst -> true
    | _ -> false
    end
  | _ -> false

let is_inductive d = 
  match d.it with
  | RelD _ -> true
  | TypD(_, _, [inst]) when is_variant_typ inst || is_alias_typ inst -> true
  | _ -> false
    
let comment_desc_def d = 
  match d.it with
  | TypD (_, _, [inst]) when is_alias_typ inst -> "Type Alias Definition"
  | TypD (_, _, [inst]) when is_variant_typ inst -> "Inductive Type Definition"
  | TypD (_, _, [inst]) when is_record_typ inst -> "Record Creation Definition"
  | TypD _ -> "Type Family Definition"
  | RecD [_] -> "Recursive Definition"
  | RecD _ -> "Recursive Definitions"
  | DecD (_, _, _, []) -> "Axiom Definition"
  | DecD _ -> "Auxiliary Definition"
  | RelD _ -> "Inductive Relations Definition"
  | HintD _ -> "Hint Definition"
  | GramD _ -> "Grammar Production Definition"

let render_unop unop = 
  match unop with
  | `NotOp   -> "!"
  | `PlusOp  -> ""
  | `MinusOp -> "0 - "
let render_binop binop = 
  match binop with
  | `AndOp   -> " && " 
  | `OrOp    -> " || "
  | `ImplOp  -> " -> "
  | `EquivOp -> " <-> "
  | `AddOp   -> " + " 
  | `SubOp   -> " - " 
  | `MulOp   -> " * " 
  | `DivOp   -> " / "
  | `ModOp   -> " % "
  | `PowOp   -> " ^ " 

let render_cmpop cmpop =
  match cmpop with
  | `EqOp -> " == "
  | `NeOp -> " != "
  | `LtOp -> " < "
  | `GtOp -> " > "
  | `LeOp -> " <= "
  | `GeOp -> " >= "

let is_atomid a =
  match a.it with
  | Xl.Atom.Atom _ -> true
  | _ -> false 

let render_atom a =
  match a.it with
  | Xl.Atom.Atom a -> a
  | _ -> ""

  let render_id a = match a with
  | "rec" -> "rec_"
  | "bool" -> "nat_of_bool"
  | "mut" | "local" | "export" | "import" | "catch" | "syntax" | "at"
    -> "«" ^ a ^ "»"
  | _ -> a

let render_mixop (m : mixop) =
  match m with
  | Xl.Mixop.Atom a -> render_atom a
  | mixop -> String.concat "" (List.map (
    fun atoms -> String.concat "" (List.filter is_atomid atoms |> List.map render_atom))
    (Xl.Mixop.flatten mixop))

let get_param_id b =
  match b.it with
  | ExpP (id, _) | TypP id | DefP (id, _, _) | GramP (id, _, _) -> id.it

(* Lean core has Int and Rat, but no Real: a use of `Real` fails to elaborate. *)
let render_numtyp nt =
  match nt with
  | `NatT -> "Nat"
  | `IntT -> "Int"
  | `RatT -> "Rat"
  | `RealT -> "Real"

(* A conversion applies to the whole operand, so the arithmetic inside it happens in
   the source type. SpecTec's downward conversions are partial; `Int.toNat` and
   `Rat.floor` agree with them on every value of the target type. *)
let render_cvt s nt1 nt2 =
  match nt1, nt2 with
  | `NatT, `IntT -> parens ("Int.ofNat " ^ s)
  | `NatT, `RatT -> parens ("Rat.ofInt (Int.ofNat " ^ s ^ ")")
  | `IntT, `RatT -> parens ("Rat.ofInt " ^ s)
  | `IntT, `NatT -> parens ("Int.toNat " ^ s)
  | `RatT, `IntT -> parens ("Rat.floor " ^ s)
  | `RatT, `NatT -> parens ("Int.toNat (Rat.floor " ^ s ^ ")")
  | _, nt2 -> parens (s ^ " : " ^ render_numtyp nt2)

let transform_case_tup e = 
  match e.it with
  | TupE exps -> exps
  | _ -> [e]

let transform_case_typ t =
  match t.it with
  | TupT typs -> List.map snd typs
  | _ -> [t]

let transform_case_args t =
  match t.it with
  | TupT typs -> typs
  | _ -> [("_" $ t.at, t)]

let get_type_args t = 
  match t.it with
  | VarT (_, args) -> args
  | _ -> error t.at ("Following type should be a variable type: " ^ Il.Print.string_of_typ t)

let rec render_param_type exp_type param = 
  match param.it with
  | ExpP (_, typ) -> render_type exp_type typ
  | TypP _ -> "Type"
  | DefP (_, params, typ) -> 
    string_of_list_suffix " -> " " -> " (render_param_type exp_type) params ^ render_type exp_type typ
  | GramP _ -> comment_parens ("Unsupported param: " ^ Il.Print.string_of_param param)

and render_type exp_type typ = 
  let rt_func = render_type exp_type in
  match typ.it with
  | VarT (id, []) -> render_id id.it
  | VarT (id, args) -> parens (render_id id.it ^ " " ^ String.concat " " (List.map (render_arg exp_type) args))
  | BoolT -> "Bool"
  | NumT nt -> render_numtyp nt
  | TextT -> "String"
  | TupT [] -> "Unit"
  | TupT typs -> parens (String.concat " × " (List.map (fun (_, t) -> rt_func t) typs))
  | IterT (t, Opt) -> parens ("Option " ^ rt_func t)
  | IterT (t, _) -> parens ("List " ^ rt_func t)

and render_exp exp_type exp =
  let r_func = render_exp exp_type in
  match exp.it with 
  | VarE id -> render_id id.it
  | BoolE b -> string_of_bool b
  | NumE (`Nat n) -> Z.to_string n
  | NumE (`Int n) when Z.sign n < 0 -> parens (Z.to_string n)
  | NumE (`Int n) -> Z.to_string n
  | NumE (`Rat n) -> parens (parens (Z.to_string (Q.num n)) ^ " / " ^ parens (Z.to_string (Q.den n)) ^ " : Rat")
  | NumE (`Real n) -> parens (string_of_float n ^ " : Real")
  | TextE s -> "\"" ^ String.escaped s ^ "\""
  | UnE (unop, _, e1) -> parens (render_unop unop ^ r_func e1)
  | BinE (binop, _, e1, e2) -> parens (r_func e1 ^ render_binop binop ^ r_func e2)
  | CmpE (cmpop, _, e1, e2) -> parens (r_func e1 ^ render_cmpop cmpop ^ r_func e2)
  | TupE [] -> "()"
  | TupE exps -> parens (String.concat ", " (List.map r_func exps))
  (* `A × B × C` is `A × (B × C)`: component `i` of an `n`-tuple is `Prod.fst` after
     `i` applications of `Prod.snd`, and the last component takes no `Prod.fst`. *)
  | ProjE (e, i) ->
    let rec proj i n s =
      if n <= 1 then s
      else if i = 0 then parens ("Prod.fst " ^ s)
      else proj (i - 1) (n - 1) (parens ("Prod.snd " ^ s))
    in
    proj i (List.length (transform_case_typ e.note)) (r_func e)
  | CaseE (m, e) when exp_type = LHS -> 
    let exps = transform_case_tup e in
    begin match exps with
    | [] -> "." ^ render_mixop m
    | _ -> parens ("." ^ render_mixop m ^ " " ^ String.concat " " (List.map r_func exps))
    end
  | CaseE (m, e) -> 
    let exps = transform_case_tup e in
    begin match exps with
    | [] -> "." ^ render_mixop m
    | _ -> parens ("." ^ render_mixop m ^ " " ^ String.concat " " (List.map r_func exps))
    end
  | UncaseE _ -> error exp.at "Encountered uncase. Run uncase-removal pass"
  | OptE (Some e) -> parens ("some " ^ r_func e)
  | OptE None -> "none"
  | TheE e -> parens ("Option.get! " ^ r_func e)
  | StrE fields -> "{ " ^ (String.concat ", " (List.map (fun (a, e) -> render_atom a ^ " := " ^ r_func e) fields)) ^ " }"
  | DotE (e, a) -> parens (r_func e ^ "." ^ render_atom a)
  | CompE (e1, e2) -> parens (r_func e1 ^ " ++ " ^ r_func e2)
  | ListE [] -> "[]"
  | ListE exps when exp_type = LHS -> square_parens (String.concat ", " (List.map r_func exps))
  | ListE exps -> parens (square_parens (String.concat ", " (List.map r_func exps)) ^ " : " ^ render_type RHS exp.note)
  | LiftE e -> parens ("Option.toList " ^ r_func e)
  (* | MemE (e1, e2) -> parens (r_func e1 ^ " ∈ " ^ r_func e2) *)
  | MemE (e1, e2) -> parens ("List.contains" ^ " " ^ r_func e2 ^ " " ^ r_func e1)
  | LenE e1 -> parens ("List.length " ^ r_func e1)
  | CatE ({it = ListE [e1]; _}, e2) when exp_type = LHS -> parens (r_func e1 ^ " :: " ^ r_func e2) 
  | CatE (e1, e2) -> parens (r_func e1 ^ " ++ " ^ r_func e2)
  | IdxE (e1, e2) -> parens (r_func e1 ^ "[" ^ r_func e2 ^ "]!")
  (* `e1[e2 : e3]` is the slice of length `e3` from index `e2`. *)
  | SliceE (e1, e2, e3) -> parens ("List.take " ^ r_func e3 ^ " (List.drop " ^ r_func e2 ^ " " ^ r_func e1 ^ ")")
  | UpdE (e1, p, e2) -> render_path_start p e1 false e2
  | ExtE (e1, p, e2) -> render_path_start p e1 true e2
  | CallE (id, args) -> parens (render_id id.it ^ " " ^ String.concat " " (List.map (render_arg exp_type) args))
  (* Iter handling *)
  (* `e^(i<n){x <- xs}` is the list of `e` at `i = 0, ..., n-1`, where `x` is `xs[i]`. *)
  | IterE (e, (ListN (n, Some i), iter_binds)) when exp_type <> LHS ->
    let body = match e.it with
      | CaseE _ -> parens (r_func e ^ " : " ^ render_type RHS e.note)
      | _ -> r_func e
    in
    parens (parens ("List.range " ^ r_func n) ^ ".map " ^
      render_lambda [parens (render_id i.it ^ " : Nat")] (render_index_lets i iter_binds body))
  | IterE (e, (ListN (n, _), [])) -> parens ("List.replicate " ^ (r_func n) ^ " " ^ (r_func e))
  | IterE (e, (_, [])) -> r_func e
  | IterE (e, _) when exp_type = LHS -> r_func e
  | IterE (e, (iter, iter_binds)) ->
    let binds = List.map (fun (id, e) -> parens (id.it ^ " : " ^ render_type exp_type (remove_iter_from_type e.note))) iter_binds in
    let iter_exps = List.map snd iter_binds in 
    let n = List.length iter_binds - 1 in
    let lst = if iter = Opt then iter_exp_opt_funcs else iter_exp_lst_funcs in
    let pred_name = match (List.nth_opt lst n) with 
    | Some s -> s
    | None -> error exp.at "Iteration exceeded the supported amount for rocq translation"
    in 
    (* A constructor in the body of the lambda needs the result type. *)
    let body = match e.it with
      | CaseE _ -> parens (r_func e ^ " : " ^ render_type RHS e.note)
      | _ -> r_func e
    in
    parens (pred_name ^ " " ^ render_lambda binds body ^ " " ^ 
    String.concat " " (List.map (render_exp exp_type) iter_exps))
  | CvtE (e1, nt1, nt2) -> render_cvt (r_func e1) nt1 nt2
  | SubE _ -> error exp.at "Encountered subtype expression. Please run sub pass"
  | IfE (cond, then_exp, else_exp) -> 
    parens ("if " ^ r_func cond ^ " then " ^ r_func then_exp ^ " else " ^ r_func else_exp)

(* `let x : T := xs[i]!; text` for every binder `x <- xs` of an indexed iteration. *)
and render_index_lets i iter_binds text =
  List.fold_right (fun (id, e) acc ->
    "let " ^ render_id id.it ^ " : " ^ render_type RHS (remove_iter_from_type e.note) ^ " := " ^
    parens (render_exp RHS e) ^ "[" ^ render_id i.it ^ "]!; " ^ acc) iter_binds text

and render_arg exp_type a = 
  match a.it with 
  | ExpA e -> render_exp exp_type e
  | TypA t -> render_type exp_type t
  | DefA id -> render_id id.it 
  | _ -> comment_parens ("Unsupported arg: " ^ Il.Print.string_of_arg a)

and render_quant exp_type q =
  match q.it with
  | ExpP (id, typ) -> parens (render_id id.it ^ " : " ^ render_type exp_type typ)
  | TypP id when exp_type = REL -> parens (render_id id.it ^ " : Type 0") ^ " " ^ square_parens ("Inhabited " ^ render_id id.it)
  | TypP id -> parens (render_id id.it ^ " : Type 0")
  | DefP (id, params, typ) ->
    parens (render_id id.it ^ " : " ^
    string_of_list_suffix " -> " " -> " (render_param_type exp_type) params ^
    render_type exp_type typ)
  | GramP _ -> comment_parens ("Unsupported quant: " ^ Il.Print.string_of_quant q)

and render_param exp_type param =
  parens (get_param_id param ^ " : " ^ render_param_type exp_type param) ^
  (match param.it with TypP id -> " " ^ square_parens ("Inhabited " ^ id.it) | _ -> "")


(* PATH Functions *)
and transform_list_path (p : path) = 
  match p.it with   
  | RootP -> []
  | IdxP (p', _) | SliceP (p', _, _) | DotP (p', _) when p'.it = RootP -> []
  | IdxP (p', _) | SliceP (p', _, _) | DotP (p', _) -> p' :: transform_list_path p'

and render_lambda binds text =
  parens ("fun " ^ String.concat " " binds ^ " => " ^ text)

and render_path_start (p : path) start_exp is_extend end_exp = 
  let paths = List.rev (p :: transform_list_path p) in
  (render_path paths (start_exp.note) p.at 0 (Some start_exp) is_extend end_exp)

and render_path (paths : path list) typ at n name is_extend end_exp = 
  let render_record_update t1 t2 t3 =
    "{ " ^ t1 ^ " with " ^ t2 ^ " := " ^ t3 ^ " }"
  in
  let r_func_e = render_exp RHS in
  let is_dot p = (match p.it with
    | DotP _ -> true
    | _ -> false 
  ) in
  let list_name num = (match name with
    | Some exp -> exp
    | None -> VarE ((var_prefix ^ string_of_int num) $ no_region) $$ no_region % typ
  ) in
  let new_name_typ = remove_iter_from_type (list_name n).note in
  let new_name = var_prefix ^ string_of_int (n + 1) in 
  match paths with
  (* End logic for extend *)
  | [{it = IdxP (_, e); _}] when is_extend -> 
    let extend_term = parens (new_name ^ " ++ " ^ r_func_e end_exp) in
    let bind = render_quant RHS (ExpP (new_name $ no_region, new_name_typ) $ no_region) in
    parens ("List.modify " ^ r_func_e (list_name n) ^ " " ^ r_func_e e ^ render_lambda [bind] extend_term)
  | [{it = DotP (_, a); _}] when is_extend -> 
    let projection_term = parens (parens (r_func_e (list_name n)) ^ "." ^ render_atom a) in
    let extend_term = parens (projection_term ^ " ++ " ^ r_func_e end_exp) in
    render_record_update (r_func_e (list_name n)) (render_atom a) extend_term
  | [{it = SliceP (_, e1, e2); _}] when is_extend -> 
    let extend_term = parens (new_name ^ " ++ " ^ r_func_e end_exp) in
    let bind = render_quant RHS (ExpP (new_name $ no_region, new_name_typ) $ no_region) in
    parens ("list_slice_update " ^ r_func_e (list_name n) ^ " " ^ r_func_e e1 ^ " " ^ r_func_e e2 ^ " " ^ render_lambda [bind] extend_term)
  (* End logic for update *)
  | [{it = IdxP (_, e); _}] -> 
    let bind = render_quant RHS (ExpP ("_" $ no_region, new_name_typ) $ no_region) in
    parens ("List.modify " ^ r_func_e (list_name n) ^ " " ^ r_func_e e ^ " " ^ render_lambda [bind] (r_func_e end_exp))
  | [{it = DotP (_, a); _}] -> 
    render_record_update (r_func_e (list_name n)) (render_atom a) (r_func_e end_exp)
  | [{it = SliceP (_, e1, e2); _}] -> 
    parens ("list_slice_update " ^ r_func_e (list_name n) ^ " " ^ r_func_e e1 ^ " " ^ r_func_e e2 ^ " " ^ r_func_e end_exp)
  (* Middle logic *)
  | {it = IdxP (_, e); note; _} :: ps -> 
    let path_term = render_path ps note at (n + 1) None is_extend end_exp in
    let new_name = var_prefix ^ string_of_int (n + 1) in 
    let bind = render_quant RHS (ExpP (new_name $ no_region, new_name_typ) $ no_region) in
    parens ("list_update_func " ^ r_func_e (list_name n) ^ " " ^ r_func_e e ^ " " ^ render_lambda [bind] path_term)
  | ({it = DotP _; note; _} as p) :: ps -> 
    let (dot_paths, ps') = list_split is_dot (p :: ps) in
    let (end_atom, dot_paths') = match List.rev dot_paths with
      | {it = DotP (_, a'); _} :: ds -> (a', ds)
      | _ -> assert false (* Impossible since it has p *)
    in
    let projection_term = List.fold_right (fun p acc -> 
      match p.it with
      | DotP (_, a') -> 
        DotE (acc, a') $$ no_region % p.note
      | _ -> error at "Should be a record access" (* Should not happen *)
    )  dot_paths' (list_name n) in
    let update_fields = String.concat "." (List.map (fun p ->
      match p.it with
      | DotP (_, a) -> render_atom a
      | _ -> error at "Should be a record access" 
    ) dot_paths) in
    let new_term = parens (parens (r_func_e projection_term) ^ "." ^ render_atom end_atom) in
    let new_exp = DotE (projection_term, end_atom) $$ no_region % note in 
    if ps' = [] 
      then (
        let final_term = if is_extend then parens (new_term ^ " ++ " ^ r_func_e end_exp) else r_func_e end_exp in
        render_record_update (r_func_e (list_name n)) update_fields final_term
      )
      else (
        let path_term = render_path ps' note at n (Some new_exp) is_extend end_exp in
        render_record_update (r_func_e (list_name n)) update_fields path_term
      )
  | ({it = SliceP (_, _e1, _e2); _} as p) :: _ps ->
    (* TODO - this is not entirely correct. Still unsure how to implement this as a term *)
    (* let new_typ = transform_type' NORMAL note in
    let path_term = render_path ps new_typ at (n + 1) None is_extend end_exp $@ transform_type' NORMAL note in
    let new_name = var_prefix ^ string_of_int (n + 1) in
    let lambda_typ = T_arrowtype [new_name_typ; new_typ] in
    T_app (T_exp_basic T_sliceupdate $@ anytype',
      [list_name n; transform_exp NORMAL e1; transform_exp NORMAL e2; T_lambda ([(new_name, new_name_typ)], path_term) $@ lambda_typ]) *)
    comment_parens (Il.Print.string_of_path p)
  (* Catch all error if we encounter empty list or RootP *)
  | _ -> error at "Paths should not be empty"

and render_binders (quants : quant list) =
  string_of_list_prefix " " " " (render_quant RHS) quants

let render_binders_ids (quants : quant list) =
  string_of_list_prefix " " " " get_param_id quants

let render_match_binders params =
  String.concat ", " (List.map get_param_id params)

let render_params params = 
  string_of_list_prefix " " " " (render_param RHS) params

(* A type parameter `X` is followed by its `[Inhabited X]` binder, which takes a
   wildcard pattern. *)
let render_match_args params args =
  let pats = List.concat (List.map2 (fun p a -> match p.it with
    | TypP _ -> [render_arg LHS a; "_"]
    | _ -> [render_arg LHS a]) params args) in
  string_of_list_prefix " " ", " Fun.id pats


let string_of_relation_args typ = 
  string_of_list "" " -> " " -> " (render_type REL) (transform_case_typ typ)
  
(* A boolean side condition as a proposition. *)
let rec render_prop exp =
  match exp.it with
  | CmpE (`EqOp, _, e1, e2) -> parens (render_exp REL e1 ^ " = " ^ render_exp REL e2)
  | CmpE (`NeOp, _, e1, e2) -> parens (render_exp REL e1 ^ " ≠ " ^ render_exp REL e2)
  | BinE (`AndOp, _, e1, e2) -> parens (render_prop e1 ^ " ∧ " ^ render_prop e2)
  | BinE (`OrOp, _, e1, e2) -> parens (render_prop e1 ^ " ∨ " ^ render_prop e2)
  | BinE (`ImplOp, _, e1, e2) -> parens (render_prop e1 ^ " → " ^ render_prop e2)
  | BinE (`EquivOp, _, e1, e2) -> parens (render_prop e1 ^ " ↔ " ^ render_prop e2)
  | UnE (`NotOp, _, e1) -> parens ("¬" ^ render_prop e1)
  | MemE (e1, e2) -> parens (render_exp REL e1 ^ " ∈ " ^ render_exp REL e2)
  | BoolE true -> "True"
  | BoolE false -> "False"
  | _ -> render_exp REL exp

let rec render_prem prem =
  let r_func = render_prem in 
  match prem.it with
  | IfPr exp -> render_prop exp
  | RulePr (id, args, _m, exp) -> parens (id.it ^
    string_of_list_prefix " " " " (render_arg REL) args ^
    string_of_list_prefix " " " " (render_exp REL) (transform_case_tup exp))
  | NegPr p -> parens ("¬" ^ r_func p)
  | ElsePr -> "True " ^ comment_parens ("Unsupported premise: otherwise") (* Will be removed by an else pass *)
  (* `p^(i<n){x <- xs}` holds when `p` holds at every `i < n`, where `x` is `xs[i]`. *)
  | IterPr (p, (ListN (n, Some i), ps)) ->
    parens ("∀ " ^ parens (render_id i.it ^ " : Nat") ^ ", " ^ render_id i.it ^ " < " ^
      render_exp REL n ^ " → " ^ render_index_lets i ps (r_func p))
  | IterPr (p, (_, [])) -> r_func p
  | IterPr (p, (iter, ps)) -> 
    let option_conversion s = if iter = Opt then parens ("Option.toList " ^ s) else s in
    let binds = List.map (fun (id, e) -> parens (id.it ^ " : " ^ render_type REL (remove_iter_from_type e.note))) ps in
    let iter_exps = List.map snd ps in 
    let n = List.length ps - 1 in
    let pred_name = match (List.nth_opt iter_prem_rels_list n) with 
    | Some s -> s
    | None -> error prem.at "Iteration exceeded the supported amount for rocq translation"
    in 
    pred_name ^ " " ^ render_lambda binds (r_func p) ^ " " ^ 
    String.concat " " (List.map (render_exp REL) iter_exps |> List.map option_conversion)
  (* The quantifiers of a `LetPr` join the quantifiers of its rule (`let_quants`). *)
  | LetPr (_, e1, e2) -> parens (render_exp REL e1 ^ " = " ^ render_exp REL e2)

let let_quants prems =
  List.concat_map (fun prem -> match prem.it with LetPr (qs, _, _) -> qs | _ -> []) prems
 
let render_typealias id binds typ = 
  "abbrev " ^ render_id id ^ render_binders binds ^ " : Type := " ^ render_type RHS typ

(* The types whose equality is decided classically: the members of a type group that occurs in
   its own constructor arguments under a type constructor (`List instr` in `instr`), for which
   `deriving DecidableEq` has no handler. *)
let classical_eq_types : StringSet.t ref = ref StringSet.empty

let deriving_clause id =
  if StringSet.mem id !classical_eq_types then "deriving Inhabited"
  else "deriving Inhabited, DecidableEq"

let rec group_typds def =
  match def.it with
  | TypD (id, _, [inst]) when is_variant_typ inst || is_record_typ inst -> [(id.it, inst)]
  | RecD defs -> List.concat_map group_typds defs
  | _ -> []

let is_nested_group typds =
  let ids = List.map fst typds in
  let rec mentions t =
    match t.it with
    | VarT (id, args) -> List.mem id.it ids || List.exists mentions_arg args
    | IterT (t', _) -> mentions t'
    | TupT ts -> List.exists (fun (_, t') -> mentions t') ts
    | _ -> false
  and mentions_arg a = match a.it with TypA t -> mentions t | _ -> false in
  let nested t =
    match t.it with
    | VarT (_, args) -> List.exists mentions_arg args
    | IterT (t', _) -> mentions t'
    | TupT ts -> List.exists (fun (_, t') -> mentions t') ts
    | _ -> false
  in
  List.exists (fun (_, inst) -> match inst.it with
    | InstD (_, _, {it = VariantT cases; _}) ->
      List.exists (fun (_, (t, _, _), _) -> List.exists (fun (_, a) -> nested a) (transform_case_args t)) cases
    | InstD (_, _, {it = StructT fields; _}) ->
      List.exists (fun (_, (t, _, _), _) -> nested t) fields
    | _ -> false) typds

let classical_instances def =
  String.concat "" (List.filter_map (fun (id, inst) ->
    if not (StringSet.mem id !classical_eq_types) then None else
    let InstD (binds, _, _) = inst.it in
    Some ("\n\nnoncomputable instance" ^ render_binders binds ^ " : DecidableEq " ^
      parens (render_id id ^ render_binders_ids binds) ^ " :=\n  fun a b => Classical.propDecidable (a = b)"))
    (group_typds def))

let render_record id binds fields = 
  let constructor_name = "MK" ^ id in
  let inhabitance_binders = render_binders binds in 
  let binders = render_binders_ids binds in 

  (* Standard Record definition *)
  "structure " ^ id ^ inhabitance_binders ^ " where " ^ constructor_name ^ " ::\n  " ^ 
  String.concat "\n  " (List.map (fun (a, (typ, _, _), _) ->
    render_atom a ^ " : " ^ render_type RHS typ) fields) ^ "\n" ^

  deriving_clause id ^ "\n\n" ^

  (* Append instance *)
  "def _append_" ^ id ^ inhabitance_binders ^ " (arg1 arg2 : " ^ parens (id ^ binders) ^ ") : " ^ render_id id ^ " where" ^ 
  "\n  " ^ String.concat "\n  " ((List.map (fun (a, (t, _, _), _) ->
    let record_id' = render_atom a in
    if (check_trivial_append !env_ref t) 
    then record_id' ^ " := " ^ "arg1." ^ record_id' ^ " ++ arg2." ^ record_id'
    else record_id' ^ " := " ^ "arg1." ^ record_id' ^ " " ^ comment_parens "FIXME - Non-trivial append"
  )) fields) ^ "\n" ^ 
  "instance : Append " ^ render_id id ^ " where\n  append arg1 arg2 := _append_" ^ id ^ " arg1 arg2\n\n"

let rec has_typ id t =
  match t.it with
  | VarT (id', _) -> id'.it = id
  | IterT (t', _) ->  has_typ id t'
  | TupT pairs -> List.exists (fun (_, t') -> has_typ id t') pairs
  | _ -> false

let render_case_typs t = 
  let typs = transform_case_args t in
  string_of_list_prefix " " " " (fun (id, t) ->
    parens (render_id id.it ^ " : " ^ render_type RHS t)) typs

let render_variant_typ id binds cases = 
  "inductive " ^ render_id id ^ render_binders binds ^ " : Type where\n  " ^
  String.concat "\n  " (List.map (fun (m, (t, _, _), _) ->
    "| " ^ render_mixop m ^ render_case_typs t ^ " : " ^ render_id id ^ render_binders_ids binds   
  )  cases) ^ 
  "\n" ^ deriving_clause id ^ "\n"

let clauses_have_same_args c1 c2 =
  match (c1.it, c2.it) with
  | (DefD (binds1, args1, _, _), DefD (binds2, args2, _, _)) ->
    Il.Eq.eq_list Il.Eq.eq_param binds1 binds2 &&
    Il.Eq.eq_list Il.Eq.eq_arg args1 args2

let group_clauses_by_same_args clauses =
  let group_helper acc clause =
    match acc with
    | [] -> [[clause]]
    | group :: rest ->
      let representative = List.hd group in
      if clauses_have_same_args representative clause then
        (group @ [clause]) :: rest
      else
        [clause] :: group :: rest
  in
  List.fold_left group_helper [] clauses |> List.rev
  
let render_function_def id params r_typ clauses = 
  let groups = group_clauses_by_same_args clauses in
  "def " ^ render_id id ^ " : ∀ " ^ render_params params ^ " , " ^ render_type RHS r_typ ^ "\n" ^
  String.concat "\n" (List.map (fun group -> match (List.hd group).it with
    | DefD (_, args, _, _) -> 
    "  |" ^ render_match_args params args ^ " =>\n    " ^
    String.concat "\n    " (List.map (fun clause ->
      let DefD (_, _, exp, prems) = clause.it in
      match prems with
      | [] -> render_exp RHS exp
      | [{it = ElsePr; _}] -> "  " ^ render_exp RHS exp
      | _ ->
        "if " ^ String.concat " && " (List.map (fun prem -> render_prem prem) prems) ^ " then\n      " ^
        render_exp RHS exp ^ "\n    else"
    ) group)
  ) groups) ^
  "\n"

(* The length premises of the iterations in a rule: every binder of `e^n` has length `n`,
   and the binders of one iteration have equal lengths (equal shape for `?`). A premise is
   emitted only when the rule quantifies every variable that it mentions. *)
let iter_length_prems quants exp prems =
  let acc = ref [] in
  let module Arg = struct
    include Il.Iter.Skip
    let add es s = acc := (es, s) :: !acc
    let len e = parens ("List.length " ^ render_exp REL e)
    let record iter binds =
      let exps = List.map snd binds in
      match iter, exps with
      | ListN (n, _), _ ->
        List.iter (fun e -> add [n; e] (parens (len e ^ " = " ^ render_exp REL n))) exps
      | (List | List1), e0 :: rest ->
        List.iter (fun e -> add [e0; e] (parens (len e0 ^ " = " ^ len e))) rest
      | Opt, e0 :: rest ->
        List.iter (fun e -> add [e0; e] (parens (parens (render_exp REL e0) ^ ".isSome = " ^
          parens (render_exp REL e) ^ ".isSome"))) rest
      | _, [] -> ()
    let visit_exp e = match e.it with
      | IterE (_, (iter, binds)) -> record iter binds
      | _ -> ()
    let visit_prem p = match p.it with
      | IterPr (_, (iter, binds)) -> record iter binds
      | _ -> ()
  end in
  let module It = Il.Iter.Make(Arg) in
  It.exp exp;
  It.prems prems;
  let bound = (Il.Free.bound_quants quants).Il.Free.varid in
  let closed e = Il.Free.Set.subset (Il.Free.free_exp e).Il.Free.varid bound in
  List.rev !acc
  |> List.filter (fun (es, _) -> List.for_all closed es)
  |> List.map snd
  |> List.fold_left (fun seen s -> if List.mem s seen then seen else seen @ [s]) []

let render_relation id params typ rules =
  "inductive " ^ id ^ render_params params ^ " : " ^ string_of_relation_args typ ^ "Prop where\n  " ^
  String.concat "\n  " (List.map (fun rule -> match rule.it with
    | RuleD (rule_id, quants, _, exp, prems) ->
      let string_prems = string_of_list "\n    " " ->\n    " " ->\n    " (render_prem) prems in
      let param_ids = List.map get_param_id params in
      let quants = List.filter (fun q -> not (List.mem (get_param_id q) param_ids)) (quants @ let_quants prems) in
      let string_prems = string_prems ^
        String.concat "" (List.map (fun s -> s ^ " ->\n    ") (iter_length_prems quants exp prems)) in
      let forall_quantifiers = string_of_list "forall " ", " " " (render_quant REL) quants in
      "| " ^ render_id rule_id.it ^ " : " ^ forall_quantifiers ^ string_prems ^ id ^
      string_of_list_prefix " " " " get_param_id params ^ " " ^
      String.concat " " (List.map (render_exp REL) (transform_case_tup exp))
  ) rules)

let render_axiom id params r_typ =
  "opaque " ^ render_id id.it ^ " : " ^
    string_of_list "forall " ", " " " (render_param RHS) params ^
    render_type RHS r_typ ^ " := opaqueDef"

let render_rel_axiom id typ =
  "opaque " ^ id.it ^ " : " ^ string_of_relation_args typ ^ "Prop"

let render_global_declaration id typ exp = 
  "def " ^ id.it ^ " : " ^ render_type RHS typ ^ " := " ^ render_exp RHS exp

let get_type_alias_id def = 
  match def.it with
  | TypD (id, _, [inst]) when is_alias_typ inst -> Some id.it
  | _ -> None

(* A clause whose only premise is `otherwise` applies when no earlier clause does, which is the
   first-match semantics of the printed `match`. *)
let has_prems c =
  match c.it with
  | DefD (_, _, _, [{it = ElsePr; _}]) -> false
  | DefD (_, _, _, prems) -> prems <> []

(* In-order traversal of args, collecting variables. Only support expressions that we expect in function patterns *)
let rec
  args_vars (args : arg list) : string list = List.concat_map arg_vars args
and
  arg_vars (arg : arg) : string list = match arg.it with
  | ExpA e -> exp_vars e
  | TypA _ -> []
  | DefA id -> [id.it]
  | _ -> [] 
and
  exp_vars (e : exp) : string list = match e.it with
  | VarE id -> [id.it]
  | CaseE (_, e1) -> exp_vars e1
  | TupE exps -> List.concat_map exp_vars exps
  | _ -> []

(* Check if the args mention a pattern variable more than once *)
let has_nonlinear_pattern c =
  match c.it with
  | DefD (binds, args, _, _) -> 
    let bound_ids = List.map get_param_id binds in
    let rec go seen (vars : string list) =
      match vars with
      | [] -> false
      | id :: rest ->
        if List.mem id bound_ids then
          if List.mem id seen then true
          else go (id :: seen) rest
        else
          go seen rest
    in
    go [] (args_vars args)

let rec is_bool_premise prem =
  match prem.it with
  | IfPr _exp -> true
  | NegPr prem -> is_bool_premise prem
  | _ -> false

let is_else_premise prem =
  match prem.it with
  | ElsePr -> true
  | _ -> false

let is_supported_clause _id clauses = 
  match List.rev clauses with
  | [] -> true 
  | [c] -> not (has_prems c)
  | last :: others -> 
    (* Printf.eprintf "Checking supported clauses; %s\n" (String.concat "\n" (List.map (Il.Print.string_of_clause id) clauses)); *)
    (let DefD (_, _, _, prems) = last.it in match prems with | [p] -> is_else_premise p | _ -> false) &&
    List.for_all (fun c -> 
      let DefD (_, _, _, prems) = c.it in
      List.for_all is_bool_premise prems
    ) others

let is_supported_function id _params _r_typ clauses = 
  List.for_all (fun c -> not (has_nonlinear_pattern c)) clauses &&
  List.for_all (is_supported_clause id) (group_clauses_by_same_args clauses)

let is_axiom def =
  match def.it with
  | DecD (_, _, _, _clauses) -> true
  | _ -> false

let is_builtin def =
    match def.it with
    | TypD (id, _, _) -> List.mem id.it builtins
    | DecD (id, _, _, _) -> List.mem id.it builtins
    | RelD (id, _, _, _, _) -> List.mem id.it builtins
    | _ ->false

let rec string_of_def def = 
  comment_parens (comment_desc_def def ^ " at: " ^ Util.Source.string_of_region def.at) ^ "\n" ^
  begin
  if is_builtin def then "/- elided, builtin -/" else
  match def.it with
  | TypD (id, _, [{it = InstD (binds, _, {it = AliasT typ; _}); _}]) -> 
    render_typealias id.it binds typ
  | TypD (id, _, [{it = InstD (binds, _, {it = StructT typfields; _}); _}])-> 
    render_record id.it binds typfields
  | TypD (id, _, [{it = InstD (binds, _, {it = VariantT typcases; _}); _}]) -> 
    render_variant_typ id.it binds typcases
  | DecD (id, [], typ, [{it = DefD ([], [], exp, _); _}]) -> 
    render_global_declaration id typ exp
  | DecD (id, params, typ, []) -> 
    render_axiom id params typ
  | DecD (id, params, typ, clauses) -> 
    if is_supported_function id params typ clauses then
      render_function_def id.it params typ clauses
    else
      render_axiom id params typ
  | RelD (id, _, _, typ, []) ->
    render_rel_axiom id typ
  | RelD (id, params, _, typ, rules) ->
    render_relation id.it params typ rules
  (* Mutual recursion *)
  | RecD defs ->
    begin match defs with
    | [] -> ""
    | [d] -> string_of_def d
    (* HACK - this is simply to deal with functions that are not supposed to be axioms.
    The functions that are supposed to be axioms should not be mutually recursive anyways.
    *)
    | (_d :: _defs') when List.exists is_axiom defs ->
      String.concat "\n\n" (List.map string_of_def defs)
    | (_d :: _defs') -> 
      "mutual\n" ^
      String.concat "\n\n" (List.map string_of_def defs) ^ "\n\n" ^ 
      "end"
    end
  | _ -> error def.at ("Unsupported def: " ^ Il.Print.string_of_def def)
  end

let exported_string = {|/- Preamble -/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
set_option match.ignoreUnusedAlts true

instance {a : Type} : Append (Option a) where
  append := fun o1 o2 => match o1 with | none => o2 | _ => o1
    
def Forall {α : Type} (R : α → Prop) (xs : List α) : Prop :=
  ∀ x ∈ xs, R x
/- `Forall₂` and `Forall₃` relate the elements at equal positions. The rules that use them
   carry the premises that the lists have equal lengths. -/
def Forall₂ {α β : Type} (R : α → β → Prop) (xs : List α) (ys : List β) : Prop :=
  ∀ x y, (x,y) ∈ List.zip xs ys → R x y
def Forall₃ {α β γ : Type} (R : α → β → γ → Prop) (xs : List α) (ys : List β) (zs : List γ) : Prop :=
  ∀ x y z, (x,y,z) ∈ List.zip xs (List.zip ys zs) → R x y z
    
macro "opaqueDef" : term => `(by first | exact Inhabited.default | (intros; exact Inhabited.default) | (intros; assumption))

/- written manually due to `BEq` constraint -/
def disjoint_ (X : Type) [BEq X] : ∀ (var_0 : (List X)), Bool
  | [] => true
  | (w :: w'_lst) => ((!(List.contains w'_lst w)) && (disjoint_ X w'_lst))

/- written manually due to `BEq` constraint -/
def setminus_ (X : Type) [BEq X] (l1 l2 : List X) : List X :=
  l1.filter (fun x => !(List.contains l2 x))

/- Sequence primitives: `s[i] = .. f` updates element `i` with `f`, `s[i : j] = bs`
   replaces the `j` elements from `i` with `bs`. -/
def list_update_func {α : Type} (l : List α) (i : Nat) (f : α → α) : List α := l.modify i f
def list_slice_update {α : Type} (l : List α) (i j : Nat) (bs : List α) : List α :=
  l.take i ++ bs ++ l.drop (i + j)
def list_map3 {α β γ δ : Type} (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | a :: as, b :: bs, c :: cs => f a b c :: list_map3 f as bs cs
  | _, _, _ => []
def option_zipWith {α β γ : Type} (f : α → β → γ) : Option α → Option β → Option γ
  | some a, some b => some (f a b)
  | _, _ => none
def option_map3 {α β γ δ : Type} (f : α → β → γ → δ) : Option α → Option β → Option γ → Option δ
  | some a, some b, some c => some (f a b c)
  | _, _, _ => none
|}


let rec prune_def def =
  match def.it with
  | GramD _ | HintD _ -> None
  | RecD defs ->
    (match List.filter_map prune_def defs with
    | [] -> None
    | defs' -> Some { def with it = RecD defs' })
  | _ -> Some def

let string_of_script (il : script) =
  env_ref := Il.Env.env_of_script il;
  let defs = List.filter_map prune_def il in
  classical_eq_types := List.fold_left (fun acc d ->
    let typds = group_typds d in
    if is_nested_group typds then List.fold_left (fun acc (id, _) -> StringSet.add id acc) acc typds
    else acc) StringSet.empty defs;
  exported_string ^
  "/- Generated Code -/\n\n" ^
  String.concat "\n\n" (List.map (fun d -> string_of_def d ^ classical_instances d) defs)