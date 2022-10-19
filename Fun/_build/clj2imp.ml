module STbl = Map.Make(String)

let tr_var v env = match v with
  | Clj.Name(x) ->
    Imp.(if STbl.mem x env then Var(STbl.find x env) else Var x)

  | Clj.CVar(n) ->

      Imp.(array_get (Var "closure") (Cst n))

let tr_expr e env functions =
  let cpt = ref (-1) in
  let vars = ref [] in
  let new_var id =
    incr cpt;
    let v = Printf.sprintf "%s_%i" id !cpt in
    vars := v :: !vars;
    v
  in

  let rec tr_expr (e: Clj.expression) (env: string STbl.t):
      Imp.sequence * Imp.expression =
    match e with
      | Clj.Cst(n) ->
        [], Imp.Cst(n)

      | Clj.Bool(b) ->
        [], Imp.Bool(b)

      | Clj.Var(v) ->
        [], tr_var v env
      | Clj.Unop(op, e) ->
        let is, te = tr_expr e env in
        (match op, te with
        | Ops.Minus, Cst n -> [], Imp.Cst(-n)
        | Ops.Not, Bool b -> [], Imp.Bool(not b)
        | _, _ -> is, Imp.Unop(op, te))

      | Clj.Binop(op, e1, e2) ->
        let is1, te1 = tr_expr e1 env in
        let is2, te2 = tr_expr e2 env in
        (match op, te1, te2 with
        | Ops.Add, Cst n, Cst m -> [], Imp.Cst(n+m)
        | Ops.Sub, Cst n, Cst m -> [], Imp.Cst(n-m)
        | Ops.Mul, Cst n, Cst m -> [], Imp.Cst(n*m)
        | Ops.Div, Cst n, Cst m -> [], Imp.Cst(n/m)
        | Ops.Eq, _, _ -> [], Imp.Bool(te1 = te2)
        | Ops.Neq, _, _ -> [], Imp.Bool(te1 != te2)
        | Ops.Lt, Cst n, Cst m -> [], Imp.Bool(n < m)
        | Ops.Le, Cst n, Cst m -> [], Imp.Bool(n <= m)
        | Ops.Gt, Cst n, Cst m -> [], Imp.Bool(n > m)
        | Ops.Ge, Cst n, Cst m -> [], Imp.Bool(n >= m)
        | Ops.And, Bool n, Bool m -> [], Imp.Bool(n && m)
        | Ops.Or, Bool n, Bool m -> [], Imp.Bool(n || m)
        | _ ->
          is1 @ is2, Imp.Binop(op, te1, te2))

      | Clj.LetIn(x, e1, e2) ->
        let lv = new_var x in
        let is1, t1 = tr_expr e1 env in
        let is2, t2 = tr_expr e2 (STbl.add x lv env) in
        Imp.(is1 @ [Set(lv, t1)] @ is2, t2)

      | Clj.Tpl(l) ->
        let p = new_var "tpl_var" in
        let rec range l n acc' acc =
          match l with
          | [] -> acc', acc
          | e::s -> let is, te = tr_expr e env in
                    range s (n+1) (acc' @ is) ((Imp.array_set (Var p) (Cst n) te)::acc)
        in
        let iss, ist = range l 0 [] [] in
        iss @ [Imp.Set(p, Imp.array_create(Cst(List.length l)))] @ (List.rev ist), Imp.Var p
      | Clj.TplGet(e, n) ->
        let l1, l2 = tr_expr e env in
         [], Imp.array_get l2 (Cst n)
    | Clj.If(e, e1, e2) ->
        (
        let is, te = tr_expr e env in
        match te with
        | Bool true ->
              let is1, te1 = tr_expr e1 env in
              is @ is1, te1
        | Bool false ->
              let is2, te2 = tr_expr e2 env in
              is @ is2, te2
        | _ ->
              let lv = new_var "cond_var" in
              let is1, te1 = tr_expr e1 env in
              let is2, te2 = tr_expr e2 env in
              is @ [Imp.If(te, is1 @ [Set(lv, te1)], is2 @ [Set(lv, te2)])], Var(lv)
        )
    | Clj.FunRef(f) ->
          let rec find_fun func =
          match func with
          | [] -> [], Imp.Var(f)
          | f'::s -> if (Imp.(f'.name) != f)
                    then find_fun s
                    else ([], Imp.Var(f'.name))

          in
          find_fun functions
    | Clj.App(e1, e2) ->
        let is2, te2 = tr_expr e2 env in
        let is, te = tr_expr e1 env in
        (match te with
        | Var s ->
                is @ is2, Imp.Call(s, [te2])
        | Deref f ->
                is @ is2, Imp.PCall(f, [te2])
        | _ -> failwith "application not possible")
    | Clj.LetRec(x, e1, e2) ->
        let is, te = tr_expr e1 env in
        let is2, te2 = tr_expr e2 env in
        is, te
  in
  let is, te = tr_expr e env in
  is, te, !vars



let tr_fdef fdef =
  let env =
    let x = Clj.(fdef.param) in
    STbl.add x ("param_" ^ x) STbl.empty
  in
  let is, te, locals = tr_expr Clj.(fdef.code) env [] in (* Ici pour les var globales *)
  Imp.({
    name = Clj.(fdef.name);
    code = is @ [Return te];
    params = ["param_" ^ Clj.(fdef.param); "closure"];
    locals = locals;
  })


let translate_program prog =
  let functions = List.map tr_fdef Clj.(prog.functions) in
  let is, te, globals = tr_expr Clj.(prog.code) STbl.empty functions in
  let main = Imp.(is @ [Expr(Call("print_int", [te]))]) in
  Imp.({main; functions; globals})
