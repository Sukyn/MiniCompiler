module VSet = Set.Make(String)

let translate_program e =
  let fdefs = ref [] in
  let new_fname =
    let cpt = ref (-1) in
    fun () -> incr cpt; Printf.sprintf "fun_%i" !cpt
  in

  let rec tr_expr (e: Fun.expression) (bvars: VSet.t):
      Clj.expression * (string * int) list =
    let cvars = ref [] in
    let new_cvar =
      let cpt = ref 0 in (* commencera à 1 *)
      fun x -> incr cpt; cvars := (x, !cpt) :: !cvars; !cpt
    in

    let rec convert_var x bvars =
      Clj.(if VSet.mem x bvars
        then Name(x)
        else if List.mem_assoc x !cvars
        then CVar(List.assoc x !cvars)
        else CVar(new_cvar x))

    and crawl e bvars = match e with
      | Fun.Cst(n) ->
        Clj.Cst(n)

      | Fun.Bool(b) ->
        Clj.Bool(b)

      | Fun.Var(x) ->
        Clj.Var(convert_var x bvars)

      | Fun.Binop(op, e1, e2) ->
        Clj.Binop(op, crawl e1 bvars, crawl e2 bvars)
      | Fun.Unop(op, e) ->
        Clj.Unop(op, crawl e bvars)
      | Fun.App(e1, e2) ->
        let te1 = crawl e1 bvars in
        let te2 = crawl e2 bvars in
        Clj.App(Clj.TplGet(te1, 0), Clj.Tpl([te2] @ [te1]))
        (* Clj.App(te1, te2) *)

      | Fun.LetIn(x, e1, e2) ->
        Clj.LetIn(x, crawl e1 bvars, crawl e2 (VSet.add x bvars))
      | Fun.LetRec(x, e1, e2) ->
        Clj.LetRec(x, crawl e1 bvars, crawl e2 bvars)
      | Fun.Tpl(l) -> Clj.Tpl(List.map (fun x -> crawl x bvars) l)

      | Fun.TplGet(e, n) -> Clj.TplGet(crawl e bvars, n)


      | Fun.Fun(x,e) ->
        (* créer une définition de fonction et l'ajouter à la reference fdefs
          pour cela créer un nouveau nom avec new_fname *)
        (* renvoyer une expression créant une clôture fonctionnelle
          note : une clôture peut être vue comme un nuplet*)
        let f = new_fname() in
        let c, vars = tr_expr e (VSet.singleton x) in
        fdefs := Clj.({name=f; code=c; param=x}) :: !fdefs;
        Clj.Tpl(Clj.FunRef(f) :: List.rev_map (fun y -> Clj.Var (convert_var y bvars)) (List.map fst vars))


      | Fun.If(e, e1, e2) ->
         Clj.If(crawl e bvars, crawl e1 bvars, crawl e2 bvars)


    in
    let te = crawl e bvars in
    te, !cvars

  in
  let code, _ = tr_expr e VSet.empty in
  Clj.({
    functions = !fdefs;
    code = code;
  })
