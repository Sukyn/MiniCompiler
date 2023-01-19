(**
   La traduction de MIMP vers AIMP réalise deux tâches principales
   - explosion des expressions en séquences d'instructions atomiques,
     en introduisant au passage des registres virtuels pour stocker les
     résultats intermédiaires des calcules
   - implémentation des conventions de passage des paramètres et résultats
     des fonctions, ainsi que des conventions de sauvegarde des registres
     physiques

   Conventions à réaliser :
   - pour la transmission des résultats : registre $v0
   - pour le passage des paramètres, AU CHOIX
     * soit tout sur la pile (premier paramètre au sommets, les suivante
       en progressant vers l'intérieur de la pile)
     * soit les quatre premiers dans les $ai, puis les suivants sur la
       pile
   - lors d'un appel de fonction, l'appelant doit gérer la sauvegarde des
     registres $ti, $ai et $v0, et l'appelé doit gérer la sauvegarde des
     registres $si

   La création des registres virtuels est faite indépendamment pour chaque
   fonction. Dans une fonction donnée, les registres virtuels sont vus
   comme des variables locales.
 *)

open Aimp

(* Traduction directe *)
let tr_unop = function
  | Mimp.Addi n -> Addi n
let tr_binop = function
  | Mimp.Add -> Add
  | Mimp.Mul -> Mul
  | Mimp.Lt  -> Lt

(* Fonction principale, de traduction d'une définition de fonction *)
let tr_fdef globals fdef  =
  (* Liste des registres virtuels. Elle est initialisée avec les variables
     locales et sera étendue à chaque création d'un nouveau registre
     virtuel. *)
  let vregs = ref Mimp.(fdef.locals) in
  (* Fonction de génération de nouveaux registres virtuels.
     Renvoie le nouveau nom, et étend la liste. *)
  let counter = ref 0 in
  let new_vreg () =
    let name = Printf.sprintf "#%i" !counter in
    vregs := name :: !vregs;
    incr counter;
    name
  in

  (* Fonction de traduction des expressions.
     Renvoie une paire (r, s) d'une séquence s et du nom r du registre
     virtuel contenant la valeur de l'expression. *)
  let rec tr_expr = function

    (* Pour une constante, on la stocke dans un registre temporaire *)
    | Mimp.Cst n ->
       let r = new_vreg() in r, Nop ++ Cst(r, n)
    (* Idem pour un booléen *)
    | Mimp.Bool b ->
       let r = new_vreg() in
       let n = if b then 1 else 0 in
       r, Nop ++ Cst(r, n)

    (* Pour les variables c'est plus compliqué *)
    | Mimp.Var x ->

       (* Il faut distinguer ici entre variables locales, paramètres et
          variables globales. *)

       (* Si c'est une variable locale*)
       if List.mem x !vregs then  
        x, Nop   (* On la charge dans x *)

       (* Si c'est un paramètre *)
       else if (List.mem x Mimp.(fdef.params)) then
           x, Nop 
  
       (* Si c'est une variable globale, on la charge *)
       else if List.mem x globals then
         let r = new_vreg() in r, Nop ++ Read(r, x)
       else
          let r = new_vreg() in r, Nop ++ Move(r, x)
    | Mimp.Unop(op, e) ->
       
        let r = new_vreg() in 
        let r1, s1 = tr_expr e in
        r, s1 ++ Unop(r, tr_unop op, r1)
    | Mimp.Binop(op, e1, e2) ->
        let r = new_vreg() in
        let r1, s1 = tr_expr e1 in
        let r2, s2 = tr_expr e2 in
        r, s1 @@ s2 ++ Binop(r, tr_binop op, r1, r2)
    | Mimp.Call(f, args) ->
       (* Il faut réaliser ici la convention d'appel : passer les arguments
          de la bonne manière, et renvoyer le résultat dans $v0. *)
       let i = ref 0 in

       (* On va renvoyer dans v0 *)
      "$v0", let s =
                (List.fold_left (fun acc s -> i := !i + 1;
                (* On push les a_i AVANT de les modifier pour pouvoir les restaurer après *)
                if !i < 4 then 
                    (match s with 
                    (* On évite de créer des registres temporaires pour les constantes *)
                    | Mimp.Cst n -> Nop ++ Push (Printf.sprintf "$a%i" !i) ++ Cst((Printf.sprintf "$a%i" !i), n) @@ acc
                    | _ -> let r, t = tr_expr s in t ++ Push (Printf.sprintf "$a%i" !i) ++ Write((Printf.sprintf "$a%i" !i), r) @@ acc
                    )
                else
                    let r, t = tr_expr s in
                    t ++ Push r @@ acc)
                Nop args) 
            in
    s
    ++ Call(f, List.length args)
                   
  in


  let rec tr_instr = function
    | Mimp.Putchar e ->
       (match e with
                      (* Putint charge directement dans a0 plutôt que de
                          passer par un registre intermediaire *)
       | Cst n -> Nop ++ Putint n
       | _ -> let r, s = tr_expr e in
              s ++ Putchar r)
    | Mimp.Set(x, e) ->
       if List.mem x globals then 
            let z, s = tr_expr e in
          s ++ Write(x, z)
       else 

          (match e with
          | Cst n -> Nop ++ Cst(x, n)
          | Var s -> Nop ++ Move(x, s)
          
          | Binop(op, e1, e2) ->
                  if e1 = e2 then (* Si les deux sont identiques, on ne les charge qu'une seule fois *)
                    (match e1 with 
                    | Var s -> if List.mem s globals then 
                                let r1, s1 = tr_expr e1 in
                                s1 ++ Binop(x, tr_binop op, r1, r1)
                              else
                                Nop ++ Binop(x, tr_binop op, s, s)
                    | _ -> 
                      let r1, s1 = tr_expr e1 in
                      s1 ++ Binop(x, tr_binop op, r1, r1))
                  else 
                    (* Il est à peu près sûr que ce code n'est pas optimal, à nettoyer, mais fonctionnel *)
                    (match e1, e2 with 
                    | Var s, Var y -> if List.mem s globals then
                                              let r1, s1 = tr_expr e1 in
                                              (if List.mem y globals 
                                              then  let r2, s2 = tr_expr e2 in
                                                    s1 @@ s2 ++ Binop(x, tr_binop op, r1, r2)
                                              else s1 ++ Binop(x, tr_binop op, r1, y))
                                          else if List.mem y globals then 
                                              let r2, s2 = tr_expr e2 in
                                              s2 ++ Binop(x, tr_binop op, s, r2)
                                          else Nop ++ Binop(x, tr_binop op, s, y)
                    | Var s, _ ->  let r2, s2 = tr_expr e2 in
                      
                                    if List.mem s globals 
                                    then let r1, s1 = tr_expr e1 in
                                        s1 @@ s2 ++ Binop(x, tr_binop op, r1, r2) 
                                    else
                                        s2 ++ Binop(x, tr_binop op, s, r2)
                    | _, Var y -> let r1, s1 = tr_expr e1 in
                                  if List.mem y globals 
                                  then let r2, s2 = tr_expr e2 in
                                      s1 @@ s2 ++ Binop(x, tr_binop op, r1, r2) 
                                    else s1 ++ Binop(x, tr_binop op, r1, y)
                    | _ ->  
                      let r1, s1 = tr_expr e1 in
                      let r2, s2 = tr_expr e2 in
                        s1 @@ s2 ++ Binop(x, tr_binop op, r1, r2))
          | Unop(op, e') ->
            (match e' with 
            | Var s -> if s = x then Nop ++ Unop(x, tr_unop op, x)
                      else let z, s = tr_expr e in
                          s ++ Write(x, z)
            | _ -> let z, s = tr_expr e in
                  s ++ Write(x, z))
          | _ ->
            let z, s = tr_expr e in
            s ++ Move(x, z)
          )

    | Mimp.If(e, s1, s2) ->
              let z, s = tr_expr e in
              let y1 = tr_seq s1 in
              let y2 = tr_seq s2 in
              s ++ If(z, y1, y2)
    | Mimp.While(e, s) ->
      let y1 = tr_seq s in
      let z, s1 = tr_expr e in
      Nop ++ While(s1, z, y1)
    | Mimp.Return e ->
       (* Le résultat renvoyé doit être placé dans $v0. *)
       (match e with 
       | Cst n -> Nop ++ Cst("$v0", n) ++ Return
       | _ -> 
            let z, s = tr_expr e in
            s ++ Move("$v0", z) ++ Return
       )
    | Mimp.Expr e ->
       let r, s = tr_expr e in
       s
  and tr_seq = function
    | []     -> Nop
    | Mimp.Return e :: s -> 
        (match e with 
        | Cst n -> Nop ++ Cst("$v0", n) ++ Return
        | _ -> 
            let z, s = tr_expr e in
            s ++ Move("$v0", z) ++ Return
        )
    | i :: s -> tr_instr i @@ tr_seq s
  in

  let code =
    (* À ce code, il faut ajouter la sauvegarde et la restauration
       des registres virtuels callee_saved. *)
    tr_seq Mimp.(fdef.code)
  in
  {
    name = Mimp.(fdef.name);
    params = Mimp.(fdef.params);
    locals = !vregs;
    code = code
  }

(* Traduction directe *)
let tr_prog p = {
    globals = Mimp.(p.globals);
    functions = List.map (tr_fdef Mimp.(p.globals)) Mimp.(p.functions)
  }
