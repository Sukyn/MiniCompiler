open Eimp
open Mips

let new_label =
  let count = ref 0 in
  fun () -> incr count; Printf.sprintf "__lab_%i" !count

let tr_fdef fdef =

  let return_label = new_label() in

  let rec tr_instr = function
    | Putchar r          -> move a0 r @@ li v0 11 @@ syscall (* Squelette de base *)
    | Putint n           -> li a0 n @@ li v0 11 @@ syscall
    | Read(rd, Global x) -> la gp x @@ lw rd 0 gp (* Ok *)
    | Read(rd, Stack i)  -> lw rd (4*i) sp 
    | Write(Global x, r) -> la gp x @@ sw r 0 gp  (* Ok *)
    | Write(Stack i, r)  -> sw r (4*i) sp 
    | Move(rd, r)        -> move rd r
    | Push r             -> sw r 0 sp @@ subi sp sp 4 (* Squelette de base *)
    | Pop n              -> addi sp sp (4*n) (* Squelette de base *)
    | GlobCst(rd, n)      -> la gp rd @@ li t0 n @@ sw t0 0 gp
    | DirCst(Stack i, n) -> li gp n @@ sw gp (4*i) sp 
    | Cst(rd, n)         -> li rd n (* Squelette de base *)
    | Unop(rd, Addi n, r)    -> addi rd r n (* Squelette de base *)
    | Binop(rd, Add, r1, r2) -> add rd r1 r2
    | Binop(rd, Mul, r1, r2) -> mul rd r1 r2
    | Binop(rd, Lt, r1, r2)  -> slt rd r1 r2
    | Call(f)            ->  jal f
    | If(r, s1, s2) ->
          let then_label = new_label()
          and end_label = new_label()
          in
          bnez r then_label
          @@ tr_seq s2
          @@ b end_label
          @@ label then_label
          @@ tr_seq s1
          @@ label end_label
    | While(s1, r, s2) ->
          let test_label = new_label()
          and code_label = new_label()
          in
          b test_label
          @@ label code_label
          @@ tr_seq s2
          @@ label test_label
          @@ tr_seq s1
          @@ bnez r code_label

    | Return ->
        b return_label

  and tr_seq (s: Eimp.sequence) = match s with
    | Nop         -> nop
    | Instr i     -> tr_instr i
    | Seq(s1, s2) -> tr_seq s1 @@ tr_seq s2
  in

  (* code de la fonction *)
  (*Stocker fp*)
  sw fp 0 sp @@ subi sp sp 4 @@
  (*Stocker ra*)
  sw ra 0 sp @@ subi sp sp 4
  (*Redéfinir fp pour représenter le pointeur de base du tableau d'activation*)
  @@ addi fp sp 8
  (*Décaler sp pour réserver l'espace nécessaire aux variables locals *)
  @@ addi sp sp (-4 * fdef.locals)
  @@ tr_seq fdef.code
  @@ label return_label
  @@ move sp fp    (* Désallocation de la pile *)
  @@ lw ra (-4) fp (* Récupération de l'adresse de retour *)
  @@ lw fp 0 fp    (* Restauration du pointeur de base de l'appelant *)
  @@ jr ra


let tr_prog prog =
  let init =
    beqz a0 "init_end"
    @@ lw a0 0 a1
    @@ jal "atoi"
    @@ label "init_end"
    @@ move a0 v0
    (* @@ sw v0 0 sp
     * @@ subi sp sp 4 *)
    @@ jal "main"
    (* Après l'exécution de la fonction "main", appel système de fin de
       l'exécution. *)
    @@ li v0 10
    @@ syscall
  and built_ins =
    (* Fonction de conversion chaîne -> entier, à base d'une boucle sur les
       caractères de la chaîne. *)
    comment "built-in atoi"
    @@ label "atoi"
    @@ li   v0 0
    @@ label "atoi_loop"
    @@ lbu  t0 0 a0
    @@ beqz t0 "atoi_end"
    @@ addi t0 t0 (-48)
    @@ bltz t0 "atoi_error"
    @@ bgei t0 10 "atoi_error"
    @@ muli v0 v0 10
    @@ add  v0 v0 t0
    @@ addi a0 a0 1
    @@ b "atoi_loop"
    @@ label "atoi_error"
    @@ li   v0 10
    @@ syscall
    @@ label "atoi_end"
    @@ jr   ra
  in

  (**
     Code principal pour générer le code MIPS associé au programme source.
   *)
  let function_codes = List.fold_right
    (fun fdef code ->
      label fdef.name @@ tr_fdef fdef @@ code)
    prog.functions nop
  in
  let text = init @@ function_codes @@ built_ins
  and data = List.fold_right
    (fun id code -> label id @@ dword [0] @@ code)
    prog.globals nop
  in

  { data; text }
