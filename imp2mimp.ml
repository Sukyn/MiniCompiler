(**
   La traduction de IMP vers MIMP rassemble deux objectifs :
   - simplifier les expressions qui peuvent l'être
   - remplacer certaines opérations génériques par des opérations
     spécifiques de MIPS.

   L'essentiel de la traduction est un morphisme direct entre les deux
   syntaxes. On utilise des "smart constructors" comme la fonction [mk_add]
   pour faire à la volée les simplifications qui peuvent être faites.
 *)

open Mimp

module Vars = Set.Make(String)
let init_var = ref Vars.empty 
let called_var = ref Vars.empty 
(* L'appel [mk_add e1 e2] doit renvoyer une expression équivalente à la
   construction [Binop(Add, e1, e2)]. La fonction [mk_add] peut simplifier
   l'expression construite tant que cela préserve le comportement du
   programme en toute circonstantes. L'expression éventuellement simplifiée
   doit donc toujours produire
   -> le même résultat,
   -> ET les mêmes effets de bord éventuels. *)
let mk_add e1 e2 = match e1, e2 with
  (* Ajouter deux entiers l'un après l'autre revient à récupérer leur somme *)
  | Cst n1, Cst n2 ->
     Cst(n1+n2)
   (* Ajouter 0 ne fait rien *)
  | Cst 0, e | e, Cst 0 ->
     e
   (* Ajouter n1 puis ajouter n2 à e revient à ajouter n1+n2 à e *)
  | Cst n1, Unop(Addi n2, e) | Unop(Addi n2, e), Cst n1 ->
     Unop(Addi(n1+n2), e)
   (* Traduction de Addi*)
  | Cst n, e | e, Cst n ->
     Unop(Addi n, e)
   (* Ajouter n1 à e1 puis N2 à e2 revient à ajouter n1+n2 à e1+e2*)
  | Unop(Addi n1, e1), Unop(Addi n2, e2) ->
     Unop(Addi(n1+n2), Binop(Add, e1, e2))
   (* Cas de base *)
  | _ ->
     Binop(Add, e1, e2)

let mk_mul e1 e2 = match e1, e2 with
   (* e*0 = 0 *)
   | Cst 0, e | e, Cst 0 -> Cst 0
   (* e*1 = 1 *)
   | Cst 1, e | e, Cst 1 -> e
   | Cst n1, Cst n2 -> Cst(n1 * n2)
(*   | Cst 2, e1 | e1, Cst 2 -> Unop(Sll 1, e1) *) (* A faire : La puissance de 2 *)
   | _, _ -> Binop(Mul, e1, e2)

let mk_comp e1 e2 = match e1, e2 with
  | Cst n1, Cst n2 -> Bool(n1 < n2)
  | _, _ -> Binop(Lt, e1, e2)

(* Traduction directe *)
let tr_binop = function
  | Imp.Add -> Add
  | Imp.Mul -> Mul
  | Imp.Lt  -> Lt

(* Traduction directe, avec appel de "smart constructors" *)
let rec tr_expr = function
  | Imp.Cst n -> Cst n
  | Imp.Bool b -> Cst (if b then 1 else 0)
  | Imp.Var x -> if (Vars.mem x !called_var) then Var x else (called_var := Vars.add x !called_var; Var x) 
  | Imp.Binop(Add, e1, e2) -> mk_add (tr_expr e1) (tr_expr e2)
  | Imp.Binop(Mul, e1, e2) -> mk_mul (tr_expr e1) (tr_expr e2)
  | Imp.Binop(Lt, e1, e2) -> mk_comp (tr_expr e1) (tr_expr e2)
  | Imp.Call(f, args) -> Call(f, List.map tr_expr args)

(* Traduction directe *)
let rec tr_instr = function
  | Imp.Putchar e -> Putchar(tr_expr e)
  | Imp.Set(x, e) -> if (Vars.mem x !init_var) then Set(x, tr_expr e) else (init_var := Vars.add x !init_var; Set(x, tr_expr e))
  | Imp.If(e, s1, s2) -> If(tr_expr e, tr_seq s1, tr_seq s2)
  | Imp.While(e, s) -> While(tr_expr e, tr_seq s)
  | Imp.Return e -> Return(tr_expr e)
  | Imp.Expr e -> Expr(tr_expr e)
and tr_seq s =
    snd(is_return s)
and is_return e1 = match e1 with 
| [] -> false, []
| Return e :: _ -> true, [Return(tr_expr(e))]
| If(e, s1, s2)::s -> let f1, sn1 = is_return s1 in
                      let f2, sn2 = is_return s2 in
                      (if f1 && f2 then 
                        true, [If(tr_expr(e), sn1, sn2)]
                      else 
                        let (v, n) = is_return s in
                        v, [If(tr_expr(e), sn1, sn2)] @ n)
| While(e, s1)::s -> let f1, sn1 = is_return s1 in
                     (if f1 then
                        true, [While(tr_expr(e), sn1)]
                     else 
                        let (v, n) = is_return s in
                        v, [While(tr_expr(e), sn1)] @ n)
| x :: s -> let v, n = is_return s in 
            v, [tr_instr x] @ n     


(* Traduction directe *)
let tr_function globals fdef  = 
  init_var := Vars.union (Vars.of_list Imp.(fdef.params)) (Vars.of_list globals);
  called_var := Vars.empty; 
  let c = tr_seq Imp.(fdef.code) in 
  Vars.iter (fun x -> (if (not (Vars.mem x !init_var)) then 
                      Printf.printf("WARNING : %s is not initialized but is used\n") x;))
             !called_var;
  {
    name = Imp.(fdef.name);
    params = Imp.(fdef.params);
    locals = Imp.(fdef.locals);
    code = c
  }

(* Traduction directe *)
let tr_program prog = {
    globals = Imp.(prog.globals);
    functions = List.map (tr_function Imp.(prog.globals)) Imp.(prog.functions) 
  }
