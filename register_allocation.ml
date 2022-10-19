open Aimp
open Graph

module VSet = Set.Make(String)

type register =
  | Actual  of string
  | Stacked of int
(*
let liveness fdef =
  let liveness = Hashtbl.create 64 in
  (* sequence s out ->
     en supposant que les variables vivantes en sortie de [s]
      sont données par [out], calcule et renvoie les variables
     vivantes en entrée de [s]
     Note : effet de bord : met à jour la table liveness pour
        toutes les instructions vues lors du calcul*)
  let rec sequence s out = match s with
    | Nop -> out
    | Instr(n, i) ->
       Hashtbl.replace liveness n out;
       instr i out
    | Seq(s1, s2) ->
       sequence s1 (sequence s2 out)
 (* instr i out ->
    en supposant que les variables vivantes en sortie de [i]
     sont données par [out], calcule et renvoie les variables
    vivantes en entrée de [i]
    Note : effet de bord : met à jour la table liveness pour
      toutes les instructions vues lors du calcul*)
  and instr i out = match i with
    | Putchar r | Write(_, r) ->
       VSet.add r out
    | Read(rd, _) | Cst(rd, _) ->
       VSet.remove rd out
    | Move(rd, r) | Unop(rd, _, r) ->
       VSet.add r (VSet.remove rd out)
    | Binop(rd, _, r1, r2) ->
      VSet.remove rd (VSet.add r1 (VSet.add r2 out))
    | Push r ->
       VSet.add r out
    | Pop _ ->
       out
    | Call(_, n) ->
       VSet.add n out
    | Return ->
       VSet.empty
    | If(r, s1, s2) ->
       let live_in_body_2 = sequence s2 out in
       sequence s1 (VSet.add r live_in_body_2)
    | While(st, r, s) ->
       let live_in_body = sequence s out in
       let live_in_test = sequence st (VSet.add r live_in_body) in
       let live_in_body = sequence s live_in_test in
       sequence st (VSet.add r live_in_body)
  in

  ignore(sequence fdef.code VSet.empty);
  (* Si le résultat précédent n'est pas VSet.empty, on a risque d'accès à
     des variables non initialisées. *)
  liveness

let v0 = "$v0"

let interference_graph fdef =
  let live_out = liveness fdef in
  let g = List.fold_left (fun g x -> Graph.add_vertex x g) Graph.empty fdef.locals in
  let rec seq s g = match s with
    | Nop -> g
    | Instr(n, i) -> instr n i g
    | Seq(s1, s2) -> seq s1 (seq s2 g)
  and instr n i g = match i with
    | Read(rd, _) | Cst(rd, _) | Unop(rd, _, _) | Binop(rd, _, _, _) ->
        (* ajouter à g une arète entre rd et chaque registre virtuel vivant en sortie *)
        let out = Hashtbl.find live_out n in
        VSet.fold
          (fun r g' -> if r <> rd then Graph.add_edge r rd Conflict g' else g')
          out
          g
    | If(_, s1, s2) ->
        seq s1 (seq s2 g)
    | While(s1, _, s2) ->
        let out = Hashtbl.find live_out n in
        VSet.fold
          (fun r g' -> VSet.fold (fun r' g'' -> (Graph.add_edge r' rd Conflict g''))) (* jsp *)
          out
          (seq s1 g)
    | Move(rd, rs) ->
       Graph.add_edge r rd Preference g
    | Putchar _ | Write _ | Return | Push _ | Pop _ ->
       g
    | Call(_, _) ->
       g
  in
  seq fdef.code g
in

type color = int VMap.t


(* Renvoie la plus petit couleur non utilisée par l'ensemble [v]. *)
let choose_color v colors =

  (List.find (fun s c -> s c) v colors

  let george x y g =
    (* Tous les voisins de r1 de degré > K sont aussi
     des voisins de r2 *)
    failwith "not implemented"


  and simplify g =
    select (VSet.find (not has_pref s && degree s < k) g) g

  and coalesce g =
    let x y = VMap.find2 () in
    (* Chercher 2 sommets liés par une arête de pref fusionnables *)
    if x <> null then
      simplify (merge_vertices x y g)
    else freeze g
  and freeze g =
    (* Chercher un sommet de degré < K et enlever ses arêtes de pref *)
    let x = VMap.find (fun s -> degree s < k) g in
    if x <> null then simplify (remove_pref s g)
    else spill g
  and spill g =
    (* Choisir un sommet peu utilisé, fort degré, into select v*)
    let x = get_le_meilleur_sommet in
    select x g
  and select x g =
    let new_g = remove_vertex x g in
    let new_s = simplify new_g in
    choose_color x new_s
  in

  simplify g)
*)


let print_colors c =
  Printf.(printf "Coloration : \n";
          VMap.iter (printf "  %s: %i\n") c)

let allocation (fdef: function_def): register Graph.VMap.t * int =
  failwith "not implemented"
