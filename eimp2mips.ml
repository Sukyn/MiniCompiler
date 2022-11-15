open Eimp
open Mips

let new_label =
  let count = ref 0 in
  fun () -> incr count; Printf.sprintf "__lab_%i" !count

let tr_fdef fdef =

  let return_label = new_label() in
  let push r =
    sw r 0 sp @@ subi sp sp 4 in
  let rec tr_instr = function
    | Putchar r          -> move a0 r @@ li v0 11 @@ syscall (* Squelette de base *)
    | Putint n           -> li a0 n @@ li v0 11 @@ syscall
    | Read(rd, Global x) -> la gp x @@ lw rd 0 gp (* Ok *)
    | Read(rd, Stack i)  -> lw rd (-4*i) sp 
    | Write(Global x, r) -> la gp x @@ sw r 0 gp  (* Ok *)
    | Write(Stack i, r)  -> sw r (-4*i) sp 
    | Move(rd, r)        -> move rd r
    | Push r             -> push r
    | Pop n              -> addi sp sp (4*n) (* Squelette de base *)
    | GlobCst(rd, n)      -> la gp rd @@ li t0 n @@ sw t0 0 gp
    | DirCst(Stack i, n) -> li gp n @@ sw gp (-4*i) sp 
    | DirCst(Global x, n) -> failwith "not supposed to happen"
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
  
  let shf = if fdef.locals < 8 then 0 else ((fdef.locals-8)*4) in
  (* code de la fonction *)
  if fdef.name = "main" then 
        (*Stocker fp*)
      push fp 
      (*Stocker ra*)
      @@ push ra
      @@ subi sp sp (shf)
      @@ move fp sp    
      (*Redéfinir fp pour représenter le pointeur de base du tableau d'activation*)
      @@ tr_seq fdef.code
      @@ label return_label
      @@ lw ra (4+shf) sp (* Récupération de l'adresse de retour *)
      @@ lw fp (8+shf) sp
      @@ move sp fp    (* Désallocation de la pile *)
      @@ jr ra
  else 
   
    push t9 
    @@ push t8
    @@ push t7
    @@ push t6
    @@ push t5
    @@ push t4
    @@ push t3
    @@ push t2
    @@ push fp 
    @@ push ra
    @@ subi sp sp (shf)
    @@ move fp sp 
    (*
  sw t9 (-4*0) sp
  @@ sw t8 (-4*1) sp
  @@ sw t7 (-4*2) sp
  @@ sw t6 (-4*3) sp
  @@ sw t5 (-4*4) sp
  @@ sw t4 (-4*5) sp
  @@ sw t3 (-4*6) sp
  @@ sw t2 (-4*7) sp
  (*Stocker fp*)
  @@ sw fp (-4*8) sp
  (*Stocker ra*)
  @@ sw ra (-4*9) sp
  (*Redéfinir fp pour représenter le pointeur de base du tableau d'activation*)
  @@ subi fp sp (4*8) 
  *)
  (*Décaler sp pour réserver l'espace nécessaire aux variables locals *)
  @@ tr_seq fdef.code
  @@ label return_label
  @@ addi sp sp (shf)
  @@ lw ra (4*1) sp (* Récupération de l'adresse de retour *)
  @@ lw fp (4*2) sp
  @@ lw t2 (4*3) sp
  @@ lw t3 (4*4) sp
  @@ lw t4 (4*5) sp
  @@ lw t5 (4*6) sp
  @@ lw t6 (4*7) sp
  @@ lw t7 (4*8) sp
  @@ lw t8 (4*9) sp
  @@ lw t9 (4*10) sp
  @@ lw a1 (4*11) sp
  @@ lw a2 (4*12) sp
  @@ lw a3 (4*13) sp
  @@ move sp fp    (* Désallocation de la pile *)
  
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
