From Coq Require Import ZArith String List.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Memdata.
From bpf.model Require Import rBPFCommType ebpf vm vm_state rBPFDecoder rBPFSyntax.
Import ListNotations.

Open Scope string_scope.

Record stack_state := {
  call_depth : int64;
  stack_pointer : int64;
  call_frames : list CallFrame;
}.

(*
Definition modu_64_rust (x y: int64) : int64 :=
  match Int64.unsigned x, Int64.unsigned y with
  | Zpos _, Zpos _ => Int64.modu x y
  | _, _ => Int64.mods x y
  end.


Definition modu_32_rust (x y: int) : int :=
  Int.repr (Z.rem (Int.unsigned x) (Int.unsigned y)).
*)

Definition eval_reg (dst : bpf_ireg) (rm : reg_map) : int64 :=
   reg_Map.get dst rm.

Fixpoint create_list {A : Type} (n : nat) (def_v : A) : list A :=
  match n with
  | O => []
  | S n' => def_v :: create_list n' def_v
  end.

Example test_create_list_0 : create_list 0 42 = nil.
Proof. reflexivity. Qed.

Example test_create_list_1 : create_list 3 "hello" = ["hello"; "hello"; "hello"].
Proof. reflexivity. Qed.

Definition MM_INPUT_START : int64 := Int64.repr 0x400000000.

Definition init_stack_state : stack_state :=
  {|
    call_depth := Int64.repr 0;
    stack_pointer := Int64.add MM_STACK_START (Int64.mul stack_frame_size max_call_depth);
    call_frames := create_list (Z.to_nat (Int64.unsigned max_call_depth))
                    {|
                      caller_saved_registers := [];
                      frame_pointer := Int64.repr 0;
                      target_pc := Int64.repr 0
                    |}
  |}.

Inductive bpf_state : Type :=
  | BPF_OK : int64 -> reg_map -> mem -> stack_state -> SBPFV -> func_map -> int64 -> int64 -> bpf_state
  | BPF_Success : int64 -> bpf_state
  | BPF_EFlag : bpf_state
  | BPF_Err : bpf_state.

Definition init_reg_map : reg_map := reg_Map.init (Int64.repr 0).

Definition init_bpf_state (rm : reg_map) (m : mem) (v : int64) (sbpfv : SBPFV) : bpf_state :=
  BPF_OK (Int64.repr 0%Z) (reg_Map.set BR10 (Int64.add MM_STACK_START (Int64.mul stack_frame_size max_call_depth)) rm)
            m init_stack_state sbpfv init_func_map (Int64.repr 0%Z) v.

Polymorphic Inductive option2 {A : Type} : Type :=
  | NOK : option2
  | OKS : A -> option2
  | OKN : option2.

Definition eval_snd_op_u32 (so : snd_op) (rm : reg_map) : int :=
  match so with
  | SOImm i => i
  | SOReg r => Int.repr (Int64.unsigned (rm r))
  end.

Definition eval_snd_op_i32 (so : snd_op) (rm : reg_map) : int :=
  match so with
  | SOImm i => i
  | SOReg r => Int.repr (Int64.signed (rm r))
  end.

Definition eval_snd_op_u64 (so : snd_op) (rm : reg_map) : int64 :=
  match so with
  | SOImm i => Int64.repr (Int.signed i)
  | SOReg r => rm r
  end.

Definition eval_snd_op_i64 (so : snd_op) (rm : reg_map) : int64 :=
  match so with
  | SOImm i => Int64.repr (Int.signed i)
  | SOReg r => rm r
  end.

(*  ALU  *)
Definition eval_alu32_aux1
   (bop : binop) (dst : bpf_ireg) (sop : snd_op) (rm : reg_map) (is_v1 : bool) : @option2 reg_map :=
  let dv : int := Int.repr (Int64.signed (eval_reg dst rm)) in 
  let sv : int := eval_snd_op_i32 sop rm in
  match bop with
  | BPF_ADD => OKS (reg_Map.set dst (Int64.repr (Int.signed (Int.add dv sv))) rm)
  | BPF_SUB => match sop with
                | (SOReg i) => OKS (reg_Map.set dst (Int64.repr (Int.signed (Int.sub dv sv))) rm)
                | _         => if is_v1 then
                                OKS (reg_Map.set dst (Int64.repr (Int.signed (Int.sub dv sv))) rm)
                               else
                                OKS (reg_Map.set dst (Int64.repr (Int.signed (Int.sub sv dv))) rm)
               end
  | BPF_MUL => OKS (reg_Map.set dst (Int64.repr (Int.signed (Int.mul dv sv))) rm)
  | _       => OKN
  end.

Definition eval_alu32_aux2
   (bop : binop) (dst : bpf_ireg) (sop : snd_op) (rm : reg_map) : @option2 reg_map :=
  let dv : int := Int.repr (Int64.unsigned (eval_reg dst rm)) in 
  let sv : int := eval_snd_op_u32 sop rm in
  match bop with
  | BPF_DIV => if (Int.eq sv Int.zero) then 
                match sop with
                  | SOImm _ => NOK
                  | _       => OKN
                end
               else
                OKS (reg_Map.set dst (Int64.repr (Int.unsigned (Int.divu dv sv))) rm)
  | BPF_OR  => OKS (reg_Map.set dst (Int64.repr (Int.unsigned (Int.or sv dv))) rm)
  | BPF_AND => OKS (reg_Map.set dst (Int64.repr (Int.unsigned (Int.and sv dv))) rm)
  | BPF_MOD => if Int.eq sv Int.zero then 
                match sop with
                  | SOImm _ => NOK
                  | _       => OKN
                end
               else
                OKS (reg_Map.set dst (Int64.repr (Int.unsigned (Int.modu dv sv))) rm)
  | BPF_XOR => OKS (reg_Map.set dst (Int64.repr (Int.unsigned (Int.xor sv dv))) rm)
  | BPF_MOV => OKS (reg_Map.set dst (Int64.repr (Int.unsigned sv)) rm)
  | BPF_LSH => OKS (reg_Map.set dst (Int64.repr (Int.unsigned (Int.shl dv (Int.and sv (Int.repr (Z.of_nat 31)))))) rm)
  | BPF_RSH => OKS (reg_Map.set dst (Int64.repr (Int.unsigned (Int.shru dv (Int.and sv (Int.repr (Z.of_nat 31)))))) rm)
  | _       => OKN
  end.

Definition eval_alu32_aux3
   (bop : binop) (dst : bpf_ireg) (sop : snd_op) (rm : reg_map) : @option2 reg_map :=
  let dv : int := Int.repr (Int64.signed (eval_reg dst rm)) in 
  let sv : int := Int.and (eval_snd_op_u32 sop rm) (Int.repr (Z.of_nat 31)) in
  match bop with
  | BPF_ARSH => OKS (reg_Map.set dst (Int64.repr (Int.unsigned (Int.and (Int.shr dv (Int.and sv (Int.repr (Z.of_nat 31)))) (Int.repr Int.max_unsigned)))) rm) 
  | _        => OKN
  end.

Definition eval_alu32
   (bop : binop) (dst : bpf_ireg) (sop : snd_op) (rm : reg_map) (is_v1 : bool) : @option2 reg_map :=
  match bop with
  | BPF_ADD  => eval_alu32_aux1 bop dst sop rm is_v1
  | BPF_SUB  => eval_alu32_aux1 bop dst sop rm is_v1
  | BPF_MUL  => if is_v1 then
                eval_alu32_aux1 bop dst sop rm is_v1
               else
                OKN
  | BPF_DIV  => if is_v1 then
                eval_alu32_aux2 bop dst sop rm
               else
                OKN
  | BPF_OR   => eval_alu32_aux2 bop dst sop rm
  | BPF_AND  => eval_alu32_aux2 bop dst sop rm
  | BPF_MOD  => if is_v1 then
                eval_alu32_aux2 bop dst sop rm
               else
                OKN
  | BPF_XOR  => eval_alu32_aux2 bop dst sop rm
  | BPF_MOV  => eval_alu32_aux2 bop dst sop rm
  | BPF_LSH  => eval_alu32_aux2 bop dst sop rm
  | BPF_RSH  => eval_alu32_aux2 bop dst sop rm
  | BPF_ARSH => eval_alu32_aux3 bop dst sop rm
  end.

Definition eval_alu64_aux1 
   (bop : binop) (dst : bpf_ireg) (sop : snd_op) (rm : reg_map) (is_v1 : bool) : @option2 reg_map :=
  let dv : int64 := eval_reg dst rm in 
  let sv : int64 := eval_snd_op_u64 sop rm in
  match bop with
  | BPF_ADD => OKS (reg_Map.set dst (Int64.add dv sv) rm)
  | BPF_SUB => match sop with
                | (SOReg i) => OKS (reg_Map.set dst (Int64.sub dv sv) rm)
                | _         => if is_v1 then
                                OKS (reg_Map.set dst (Int64.sub dv sv) rm)
                               else
                                OKS (reg_Map.set dst (Int64.sub sv dv) rm)
               end
  | BPF_MUL => OKS (reg_Map.set dst (Int64.mul dv sv) rm)
  | BPF_DIV => if (Int64.eq sv Int64.zero) then
                match sop with
                  | SOImm _ => NOK
                  | _       => OKN
                end
               else
                OKS (reg_Map.set dst (Int64.divu dv sv) rm)
  | BPF_OR  => OKS (reg_Map.set dst (Int64.or sv dv) rm)
  | BPF_AND => OKS (reg_Map.set dst (Int64.and sv dv) rm)
  | BPF_MOD => if Int64.eq sv Int64.zero then
                match sop with
                  | SOImm _ => NOK
                  | _       => OKN
                end
               else
                OKS (reg_Map.set dst (Int64.modu dv sv) rm)
  | BPF_XOR => OKS (reg_Map.set dst (Int64.xor sv dv) rm)
  | BPF_MOV => OKS (reg_Map.set dst sv rm)
  | _       => OKN
  end.

Definition eval_alu64_aux2
   (bop : binop) (dst : bpf_ireg) (sop : snd_op) (rm : reg_map) : @option2 reg_map :=
  let dv : int64 := eval_reg dst rm in 
  let sv : int := Int.and (eval_snd_op_i32 sop rm) (Int.repr (Z.of_nat 63)) in
  match bop with
  | BPF_LSH => OKS (reg_Map.set dst (Int64.shl dv (Int64.repr (Int.unsigned sv))) rm)
  | BPF_RSH => OKS (reg_Map.set dst (Int64.shru dv (Int64.repr (Int.unsigned sv))) rm)
  | _       => OKN
  end.

Definition eval_alu64_aux3
   (bop : binop) (dst : bpf_ireg) (sop : snd_op) (rm : reg_map) : @option2 reg_map :=
  let dv : int64 := eval_reg dst rm in 
  let sv : int := Int.and (eval_snd_op_u32 sop rm) (Int.repr (Z.of_nat 63)) in
  match bop with
  | BPF_ARSH => OKS (reg_Map.set dst (Int64.shr dv (Int64.repr (Int.unsigned sv))) rm) 
  | _        => OKN
  end.

Definition eval_add64_imm_R10
  (i : int) (ss : stack_state) (is_v1 : bool) : option stack_state :=
  let sp := stack_pointer ss in
  if negb is_v1 then
    Some {| 
      call_depth := call_depth ss;
      stack_pointer := Int64.add sp (Int64.repr (Int.signed i));
      call_frames := call_frames ss
    |}
  else
    None.

Definition eval_alu64
   (bop : binop) (dst : bpf_ireg) (sop : snd_op) (rm : reg_map) (is_v1 : bool) : @option2 reg_map :=
  match bop with
  | BPF_ADD  => eval_alu64_aux1 bop dst sop rm is_v1
  | BPF_SUB  => eval_alu64_aux1 bop dst sop rm is_v1
  | BPF_MUL  => if is_v1 then
                eval_alu64_aux1 bop dst sop rm is_v1
               else
                OKN
  | BPF_DIV  => if is_v1 then
                eval_alu64_aux1 bop dst sop rm is_v1
               else
                OKN
  | BPF_OR   => eval_alu64_aux1 bop dst sop rm is_v1
  | BPF_AND  => eval_alu64_aux1 bop dst sop rm is_v1
  | BPF_MOD  => if is_v1 then
                eval_alu64_aux1 bop dst sop rm is_v1
               else
                OKN
  | BPF_XOR  => eval_alu64_aux1 bop dst sop rm is_v1
  | BPF_MOV  => eval_alu64_aux1 bop dst sop rm is_v1
  | BPF_LSH  => eval_alu64_aux2 bop dst sop rm
  | BPF_RSH  => eval_alu64_aux2 bop dst sop rm
  | BPF_ARSH => eval_alu64_aux3 bop dst sop rm
  end.

Definition eval_neg32
  (dst : bpf_ireg) (rm : reg_map) (is_v1 : bool) : @option2 reg_map :=
  if is_v1 then
    let dv : int := Int.repr (Int64.signed (eval_reg dst rm)) in
    OKS (reg_Map.set dst (Int64.and (Int64.repr (Int.unsigned (Int.neg dv))) (Int64.repr Int.max_unsigned)) rm)
  else
    OKN.

Definition eval_neg64
  (dst : bpf_ireg) (rm : reg_map) (is_v1 : bool) : @option2 reg_map :=
  if is_v1 then
    let dv : int64 := eval_reg dst rm in
    OKS (reg_Map.set dst (Int64.neg dv) rm)
  else
    OKN.

Definition eval_le
  (dst : bpf_ireg) (imm : int) (rm : reg_map) (is_v1 : bool) : @option2 reg_map :=
  if is_v1 then
    let dv := eval_reg dst rm in
    if Int.eq imm (Int.repr (Z.of_nat 16)) then
      match word_of_byte_list (byte_list_of_word (Int16.repr (Int64.unsigned dv))) with
      | None => OKN
      | Some v => OKS (reg_Map.set dst (Int64.repr (Int16.unsigned v)) rm)
      end
    else if Int.eq imm (Int.repr (Z.of_nat 32)) then
      match int_of_byte_list (byte_list_of_int (Int.repr (Int64.unsigned dv))) with
      | None => OKN
      | Some v => OKS (reg_Map.set dst (Int64.repr (Int.unsigned v)) rm)
      end
    else if Int.eq imm (Int.repr (Z.of_nat 64)) then
      match int64_of_byte_list (byte_list_of_int64 dv) with
      | None => OKN
      | Some v => OKS (reg_Map.set dst v rm)
      end
    else
      OKN
  else
    OKN.

Definition eval_be 
  (dst : bpf_ireg) (imm : int) (rm : reg_map) (is_v1 : bool) : @option2 reg_map :=
  if is_v1 then
    let dv := eval_reg dst rm in
    if Int.eq imm (Int.repr (Z.of_nat 16)) then
      match word_of_byte_list (rev (byte_list_of_word (Int16.repr (Int64.unsigned dv)))) with
      | None => OKN
      | Some v => OKS (reg_Map.set dst (Int64.repr (Int16.unsigned v)) rm)
      end
    else if Int.eq imm (Int.repr (Z.of_nat 32)) then
      match int_of_byte_list (rev (byte_list_of_int (Int.repr (Int64.unsigned dv)))) with
      | None => OKN
      | Some v => OKS (reg_Map.set dst (Int64.repr (Int.unsigned v)) rm)
      end
    else if Int.eq imm (Int.repr (Z.of_nat 64)) then
      match int64_of_byte_list (rev (byte_list_of_int64 dv)) with
      | None => OKN
      | Some v => OKS (reg_Map.set dst v rm)
      end
    else
      OKN
  else
    OKN.

Definition eval_hor64 
  (dst : bpf_ireg) (imm : int) (rm : reg_map) (is_v1 : bool) : @option2 reg_map :=
  if is_v1 then
    OKN
  else
    let dv : int64 := eval_reg dst rm in
    let dv2 := Int64.or dv (Int64.shl (Int64.repr (Int.unsigned imm)) (Int64.repr (Z.of_nat 32))) in
    OKS (reg_Map.set dst dv2 rm).

(*  PQR  *)
Definition eval_pqr32_aux1 
  (pop : pqrop) (dst : bpf_ireg) (sop : snd_op) (rm : reg_map) : @option2 reg_map :=
  let dv : int := Int.repr (Int64.signed (eval_reg dst rm)) in
  let sv : int := eval_snd_op_i32 sop rm in
  match pop with
  | BPF_LMUL => OKS (reg_Map.set dst (Int64.repr (Int.unsigned (Int.mul dv sv))) rm)
  | BPF_SDIV => 
      if Z.eqb (Int.signed sv) Z0 then
        match sop with
        | SOImm _ => NOK
        | _ => OKN
        end
      else
        OKS (reg_Map.set dst (Int64.repr (Int.signed (Int.divs dv sv))) rm)
  | BPF_SREM => 
      if Z.eqb (Int.signed sv) Z0 then
        match sop with
        | SOImm _ => NOK
        | _ => OKN
        end
      else
        OKS (reg_Map.set dst (Int64.repr (Int.signed (Int.mods dv sv))) rm)
  | _ => OKN
  end.

Definition eval_pqr32_aux2 
  (pop : pqrop) (dst : bpf_ireg) (sop : snd_op) (rm : reg_map) : @option2 reg_map :=
  let dv : int := Int.repr (Int64.unsigned (eval_reg dst rm)) in
  let sv : int := eval_snd_op_u32 sop rm in
  match pop with
  | BPF_UDIV =>
      if Z.eqb (Int.signed sv) Z0 then
        match sop with
        | SOImm _ => NOK
        | _ => OKN
        end
      else
        OKS (reg_Map.set dst (Int64.repr (Int.unsigned (Int.divu dv sv))) rm)
  | BPF_UREM => 
      if Z.eqb (Int.signed sv) Z0 then
        match sop with
        | SOImm _ => NOK
        | _ => OKN
        end
      else
        OKS (reg_Map.set dst (Int64.repr (Int.unsigned (Int.modu dv sv))) rm)
  | _ => OKN
  end.

Definition eval_pqr32
  (pop : pqrop) (dst : bpf_ireg) (sop : snd_op) (rm : reg_map) (is_v1 : bool) : @option2 reg_map :=
  if is_v1 then
    OKN
  else
    match pop with
    | BPF_LMUL =>  eval_pqr32_aux1 pop dst sop rm
    | BPF_UDIV =>  eval_pqr32_aux2 pop dst sop rm
    | BPF_UREM =>  eval_pqr32_aux2 pop dst sop rm
    | BPF_SDIV =>  eval_pqr32_aux1 pop dst sop rm
    | BPF_SREM =>  eval_pqr32_aux1 pop dst sop rm
  end.

Definition eval_pqr64_aux1 
  (pop : pqrop) (dst : bpf_ireg) (sop : snd_op) (rm : reg_map) : @option2 reg_map :=
  let dv : int64 := eval_reg dst rm in
  let sv : int64 := eval_snd_op_u64 sop rm in
  match pop with
  | BPF_LMUL => OKS (reg_Map.set dst (Int64.mul dv sv) rm)
  | BPF_UDIV => 
      if Z.eqb (Int64.signed sv) Z0 then
        match sop with
        | SOImm _ => NOK
        | _ => OKN
        end
      else
        OKS (reg_Map.set dst (Int64.divu dv sv) rm)
  | BPF_UREM => 
      if Z.eqb (Int64.signed sv) Z0 then
        match sop with
        | SOImm _ => NOK
        | _ => OKN
        end
      else
        OKS (reg_Map.set dst (Int64.modu dv sv) rm)
  | _ => OKN
  end.

Definition eval_pqr64_aux2 
  (pop : pqrop) (dst : bpf_ireg) (sop : snd_op) (rm : reg_map) : @option2 reg_map :=
  let dv : int64 := eval_reg dst rm in
  let sv : int64 := eval_snd_op_i64 sop rm in
  match pop with
  | BPF_SDIV =>
      if Z.eqb (Int64.signed sv) Z0 then
        match sop with
        | SOImm _ => NOK
        | _ => OKN
        end
      else
        OKS (reg_Map.set dst (Int64.divs dv sv) rm)
  | BPF_SREM => 
      if Z.eqb (Int64.signed sv) Z0 then
        match sop with
        | SOImm _ => NOK
        | _ => OKN
        end
      else
        OKS (reg_Map.set dst (Int64.mods dv sv) rm)
  | _ => OKN
  end.

Definition eval_pqr64
  (pop : pqrop) (dst : bpf_ireg) (sop : snd_op) (rm : reg_map) (is_v1 : bool) : @option2 reg_map :=
  if is_v1 then
    OKN
  else
    match pop with
    | BPF_LMUL =>  eval_pqr64_aux1 pop dst sop rm
    | BPF_UDIV =>  eval_pqr64_aux1 pop dst sop rm
    | BPF_UREM =>  eval_pqr64_aux1 pop dst sop rm
    | BPF_SDIV =>  eval_pqr64_aux2 pop dst sop rm
    | BPF_SREM =>  eval_pqr64_aux2 pop dst sop rm
  end.

Definition eval_pqr64_2
  (pop2 : pqrop2) (dst : bpf_ireg) (sop : snd_op) (rm : reg_map) (is_v1 : bool) : @option2 reg_map :=
  if is_v1 then
    OKN
  else
    let dv : int64 := eval_reg dst rm in
    let sv : int64 := eval_snd_op_u64 sop rm in
    match pop2 with
    | BPF_UHMUL =>  OKS (reg_Map.set dst (Int64.mulhu dv sv) rm)
    | BPF_SHMUL =>  OKS (reg_Map.set dst (Int64.mulhs dv sv) rm)
  end.

(*  MEM  *)
Definition concrete_addr_to_abstract_addr (addr: int64) (b: block): val :=
  Vptr b (Ptrofs.of_int64u addr).
(*(Int64.sub addr MM_INPUT_START)).*)

Definition memory_chunk_value_of_int64 (mc : memory_chunk) (v : int64) : val :=
  match mc with
  | Mint8unsigned | Mint16unsigned | Mint32 => Vint (Int.repr (Int64.unsigned v))
  | Mint64 => Vlong v
  | _ => Vundef
  end.

Definition eval_store
  (chk : memory_chunk) (dst : bpf_ireg) (sop : snd_op) (off : off_ty) (rm : reg_map) (m : mem) (b : block) : option mem :=
  let dv : int64 := eval_reg dst rm in
  let vm_addr : int64 := Int64.add dv (Int64.repr (Int16.signed off)) in
  let sv : int64 :=  eval_snd_op_u64 sop rm in
  Mem.storev chk m (concrete_addr_to_abstract_addr vm_addr b) (memory_chunk_value_of_int64 chk sv).

Definition eval_load 
  (chk : memory_chunk) (dst : bpf_ireg) (src : bpf_ireg) (off : off_ty) (rm : reg_map) (m : mem) (b : block) : option reg_map :=
  let sv : int64 := eval_snd_op_u64 (SOReg src) rm in
  let vm_addr : int64 := Int64.add sv (Int64.repr (Int16.signed off)) in
  let v :=  Mem.loadv chk m (concrete_addr_to_abstract_addr vm_addr b) in
  match v with
  | Some Vundef => None
  | Some (Vint v') => Some (reg_Map.set dst (Int64.repr (Int.unsigned v')) rm)
  | Some (Vlong v') => Some (reg_Map.set dst v' rm)
  | _ => None
  end.

Definition eval_load_imm
  (dst : bpf_ireg) (imm1 : int) (imm2 : int) (rm : reg_map) : reg_map :=
  let v : int64 := Int64.or (Int64.and (Int64.repr (Int.unsigned imm1)) (Int64.repr 0xffffffff%Z)) (bit_left_shift_int64 (Int64.repr (Int.unsigned imm2)) 32) in
  reg_Map.set dst v rm.

(*  JUMP  *)
Definition eval_jmp
  (cond : condition) (dst : bpf_ireg) (sop : snd_op) (rm : reg_map) : bool :=
  let udv : int64 := eval_reg dst rm in
  let usv : int64 := eval_snd_op_u64 sop rm in
  let sdv : int64 := eval_reg dst rm in
  let ssv : int64 := eval_snd_op_i64 sop rm in
  match cond with
  | Eq  => Int64.eq udv usv
  | Gt  => Int64.cmpu Cgt udv usv
  | Ge  => Int64.cmpu Cge udv usv
  | Lt  => Int64.cmpu Clt udv usv
  | Le  => Int64.cmpu Cle udv usv
  | SEt => negb (Int64.eq (Int64.and udv usv) Int64.zero)
  | Ne  => negb (Int64.eq udv usv)
  | SGt  => Int64.cmp Cgt sdv ssv
  | SGe  => Int64.cmp Cge sdv ssv
  | SLt  => Int64.cmp Clt sdv ssv
  | SLe  => Int64.cmp Cle sdv ssv
  end.

Definition list_update {A : Type} (l : list A) (n : nat) (x : A) : list A :=
  firstn n l ++ [x] ++ skipn (S n) l.

(*  CALL  *)
Definition push_frame 
  (rm : reg_map) (ss : stack_state) (is_v1 : bool) (pc : int64) (enable_stack_frame_gaps : bool) : (option stack_state) * reg_map :=
  let npc := Int64.add pc (Int64.repr 1%Z) in
  let fp := eval_reg BR10 rm in
  let caller := [eval_reg BR6 rm; eval_reg BR7 rm; eval_reg BR8 rm; eval_reg BR9 rm] in
  let frame := {|
    caller_saved_registers := caller;
    frame_pointer := fp;
    target_pc := npc
  |} in
  let update1 := Int64.add (call_depth ss) (Int64.repr 1%Z) in
  if Int64.eq update1 max_call_depth then
    (None , rm)
  else
    let update2 := 
      if is_v1 then 
        if enable_stack_frame_gaps then 
          Int64.add (stack_pointer ss) (Int64.mul stack_frame_size (Int64.repr 2))
        else 
          Int64.add (stack_pointer ss) stack_frame_size
      else 
        stack_pointer ss in
    let update3 := 
      list_update (call_frames ss) (Z.to_nat (Int64.unsigned (call_depth ss))) frame in
    let new_stack_state := {|
      call_depth := update1;
      stack_pointer := update2;
      call_frames := update3
    |} in
    let updated_reg_map := reg_Map.set BR10 update2 rm in
    (Some new_stack_state, updated_reg_map).

Definition eval_call_reg (src : bpf_ireg) (imm : int) (rm : reg_map) (ss : stack_state) (is_v1 : bool)
  (pc : int64) (fm : func_map) (enable_stack_frame_gaps : bool) (program_vm_addr : int64) : option (int64 * reg_map * stack_state) :=
  match nat_to_bpf_ireg (Z.to_nat (Int.unsigned imm)) with
  | None => None
  | Some iv =>
      let pc1 := 
        if is_v1 then
          eval_reg iv rm
        else
          eval_reg src rm in
      let (x , rm') := push_frame rm ss is_v1 pc enable_stack_frame_gaps in
      match x with
      | None => None
      | Some ss' =>
          if Int64.lt pc1 program_vm_addr then
            None
          else
            let next_pc := Int64.divu (Int64.sub pc1 program_vm_addr) (Int64.repr (Z.of_nat INSN_SIZE)) in
              Some (next_pc, rm', ss')

      end
  end.

Definition eval_call_imm (pc : int64) (src : bpf_ireg) (imm : int) (rm : reg_map) (ss : stack_state) (is_v1 : bool)
  (fm : func_map) (enable_stack_frame_gaps : bool) : option (int64 * reg_map * stack_state) :=
  let pc_option :=
    if reg_eq src BR0 then
      get_function_registry imm fm
    else
      Some (Int64.repr (Int.signed imm)) in
  match pc_option with
  | None => None
  | Some npc =>
      let (x, rm') := push_frame rm ss is_v1 pc enable_stack_frame_gaps in
      match x with
      | None => None
      | Some ss' => Some (npc, rm', ss')
      end
  end.

Definition default_frame : CallFrame :=
  {| caller_saved_registers := []; frame_pointer := Int64.zero; target_pc := Int64.zero |}.

Definition pop_frame (ss : stack_state) : CallFrame :=
  let depth := Z.to_nat (Int64.unsigned (Int64.sub (call_depth ss) Int64.one)) in
  match List.nth_error (call_frames ss) depth with
  | None => default_frame
  | Some frame => frame
  end.

(*  EXIT  *)
Definition eval_exit (rm : reg_map) (ss : stack_state) (is_v1 : bool) : (int64 * reg_map * stack_state) :=
  let x := Int64.sub (call_depth ss) Int64.one in
  match List.nth_error (call_frames ss) (Z.to_nat (Int64.unsigned x)) with
  | None =>
      (Int64.zero, rm, ss)
  | Some frame =>
      let rm' :=
        reg_Map.set BR10 (frame_pointer frame)
          (reg_Map.set BR9 (List.nth 3 (caller_saved_registers frame) Int64.zero)
            (reg_Map.set BR8 (List.nth 2 (caller_saved_registers frame) Int64.zero)
              (reg_Map.set BR7 (List.nth 1 (caller_saved_registers frame) Int64.zero)
                (reg_Map.set BR6 (List.nth 0 (caller_saved_registers frame) Int64.zero) rm)))) in
      let y :=
        if is_v1 then
          Int64.sub (stack_pointer ss) (Int64.mul (Int64.repr 2) stack_frame_size)
        else
          stack_pointer ss in
      let z := List.removelast (call_frames ss) in
      let ss' := {| 
        call_depth := x; 
        stack_pointer := y; 
        call_frames := z 
      |} in
      let pc := target_pc frame in
      (pc, rm', ss')
  end.

(*  STEP  *)
Definition step (pc : int64) (ins : bpf_instruction) (rm : reg_map) (m : mem) (ss : stack_state) (sv : SBPFV) (fm : func_map)
  (enable_stack_frame_gaps : bool) (program_vm_addr : int64) (cur_cu : int64) (remain_cu : int64) (b: block) : bpf_state :=
  let is_v1 := 
    match sv with
    | V1 => true
    | _  => false
    end in
  match ins with
  | BPF_ALU bop d sop =>
      match eval_alu32 bop d sop rm is_v1 with
      | NOK => BPF_Err
      | OKN => BPF_EFlag
      | OKS rm' => BPF_OK (Int64.add pc Int64.one) rm' m ss sv fm (Int64.add cur_cu Int64.one) remain_cu
      end
  | BPF_ALU64 bop d sop =>
      match eval_alu64 bop d sop rm is_v1 with
      | NOK => BPF_Err
      | OKN => BPF_EFlag
      | OKS rm' => BPF_OK (Int64.add pc Int64.one) rm' m ss sv fm (Int64.add cur_cu Int64.one) remain_cu
      end
  | BPF_ADD_STK i =>
      match eval_add64_imm_R10 i ss is_v1 with
      | None => BPF_Err
      | Some ss' => BPF_OK (Int64.add pc Int64.one) rm m ss' sv fm (Int64.add cur_cu Int64.one) remain_cu
      end
  | BPF_LE dst imm =>
      match eval_le dst imm rm is_v1 with
      | NOK => BPF_Err
      | OKN => BPF_EFlag
      | OKS rm' => BPF_OK (Int64.add pc Int64.one) rm' m ss sv fm (Int64.add cur_cu Int64.one) remain_cu
      end
  | BPF_BE dst imm =>
      match eval_be dst imm rm is_v1 with
      | NOK => BPF_Err
      | OKN => BPF_EFlag
      | OKS rm' => BPF_OK (Int64.add pc Int64.one) rm' m ss sv fm (Int64.add cur_cu Int64.one) remain_cu
      end
  | BPF_NEG32_REG dst =>
      match eval_neg32 dst rm is_v1 with
      | NOK => BPF_Err
      | OKN => BPF_EFlag
      | OKS rm' => BPF_OK (Int64.add pc Int64.one) rm' m ss sv fm (Int64.add cur_cu Int64.one) remain_cu
      end
  | BPF_NEG64_REG dst =>
      match eval_neg64 dst rm is_v1 with
      | NOK => BPF_Err
      | OKN => BPF_EFlag
      | OKS rm' => BPF_OK (Int64.add pc Int64.one) rm' m ss sv fm (Int64.add cur_cu Int64.one) remain_cu
      end
  | BPF_LDX chk dst sop off =>
      match eval_load chk dst sop off rm m b with
      | None => BPF_EFlag
      | Some rm' => BPF_OK (Int64.add pc Int64.one) rm' m ss sv fm (Int64.add cur_cu Int64.one) remain_cu
      end
  | BPF_ST chk dst sop off =>
      match eval_store chk dst sop off rm m b with
      | None => BPF_EFlag
      | Some m' => BPF_OK (Int64.add pc Int64.one) rm m' ss sv fm (Int64.add cur_cu Int64.one) remain_cu
      end
  | BPF_LD_IMM dst imm1 imm2 =>
      let rm' := eval_load_imm dst imm1 imm2 rm in
      BPF_OK (Int64.add pc (Int64.repr 2%Z)) rm' m ss sv fm (Int64.add cur_cu Int64.one) remain_cu
  | BPF_PQR pop dst sop =>
      match  eval_pqr32 pop dst sop rm is_v1 with
      | NOK => BPF_Err
      | OKN => BPF_EFlag
      | OKS rm' => BPF_OK (Int64.add pc Int64.one) rm' m ss sv fm (Int64.add cur_cu Int64.one) remain_cu
      end
  | BPF_PQR64 pop dst sop =>
      match eval_pqr64 pop dst sop rm is_v1 with
      | NOK=> BPF_Err
      | OKN=> BPF_EFlag
      | OKS rm' => BPF_OK (Int64.add pc Int64.one) rm' m ss sv fm (Int64.add cur_cu Int64.one) remain_cu
      end
  | BPF_PQR2 pop dst sop =>
      match  eval_pqr64_2 pop dst sop rm is_v1 with
      | NOK => BPF_Err
      | OKN => BPF_EFlag
      | OKS rm' => BPF_OK (Int64.add pc Int64.one) rm' m ss sv fm (Int64.add cur_cu Int64.one) remain_cu
      end
  | BPF_HOR64_IMM dst imm =>
      match eval_hor64 dst imm rm is_v1 with
      | NOK => BPF_Err
      | OKN => BPF_EFlag
      | OKS rm' => BPF_OK (Int64.add pc Int64.one) rm' m ss sv fm (Int64.add cur_cu Int64.one) remain_cu
      end

  | BPF_JA off =>
      BPF_OK (Int64.add (Int64.add pc (Int64.repr (Int16.signed off))) Int64.one) rm m ss sv fm (Int64.add cur_cu Int64.one) remain_cu

  | BPF_JUMP cond bpf_ireg sop off =>
      if eval_jmp cond bpf_ireg sop rm then
        BPF_OK (Int64.add (Int64.add pc (Int64.repr (Int16.signed off))) Int64.one) rm m ss sv fm (Int64.add cur_cu Int64.one) remain_cu
      else
        BPF_OK (Int64.add pc Int64.one) rm m ss sv fm (Int64.add cur_cu Int64.one) remain_cu
  | BPF_CALL_IMM src imm =>
      match eval_call_imm pc src imm rm ss is_v1 fm enable_stack_frame_gaps with
      | None => BPF_EFlag
      | Some (pc', rm', ss') => BPF_OK pc' rm' m ss' sv fm (Int64.add cur_cu Int64.one) remain_cu
      end
  | BPF_CALL_REG src imm =>
      match eval_call_reg src imm rm ss is_v1 pc fm enable_stack_frame_gaps program_vm_addr with
      | None => BPF_EFlag
      | Some (pc', rm', ss') => BPF_OK pc' rm' m ss' sv fm (Int64.add cur_cu Int64.one) remain_cu
      end
  | BPF_EXIT =>
      if Int64.eq (call_depth ss) Int64.zero then
        if Int64.cmpu Cgt cur_cu remain_cu then
          BPF_EFlag
        else
          BPF_Success (rm BR0)
      else
        let result := eval_exit rm ss is_v1 in
        match result with
        | (pc', rm', ss') =>
            BPF_OK pc' rm' m ss' sv fm (Int64.add cur_cu Int64.one) remain_cu
        end
  end.

Fixpoint bpf_interp 
  (n : nat) (prog : bpf_bin) (st : bpf_state) (enable_stack_frame_gaps : bool) (program_vm_addr : int64) (b: block) : bpf_state :=
  match n with
  | O => BPF_EFlag
  | S n' =>
      match st with
      | BPF_EFlag => BPF_EFlag
      | BPF_Err => BPF_Err
      | BPF_Success v => BPF_Success v
      | BPF_OK pc rm m ss sv fm cur_cu remain_cu =>
          if (Int64.lt pc (Int64.repr (Z.of_nat (List.length prog)))) then
            if (Int64.cmp Cge cur_cu remain_cu) then
              BPF_EFlag
            else
              match rbpf_decoder (Z.to_nat (Int64.unsigned pc)) prog with
              | None => BPF_EFlag
              | Some ins =>
                  let st1 := step pc ins rm m ss sv fm enable_stack_frame_gaps program_vm_addr cur_cu remain_cu b in
                  bpf_interp n' prog st1 enable_stack_frame_gaps program_vm_addr b
              end
          else BPF_EFlag
      end
  end.

Definition Z_to_byte_list (l : list Z) : list byte :=
  map (fun i => Byte.repr i) l.

Definition int_to_int64_list (l : list int) : list int64 :=
  map (fun i => Int64.repr (Int.unsigned i)) l.

Fixpoint get_bytes (l : list byte) : list memval :=
  match l with
  | nil => nil
  | h :: t => Byte h :: get_bytes t
  end.

Definition byte_list_to_mem (l : list byte) (m : mem) (b : block) (ofs : Z): mem :=
  match Mem.storebytes m b ofs (get_bytes l) with
  | None => m
  | Some m' => m'
  end.


Definition Zlist_to_reg_map (l : list Z) : reg_map :=
  fun i => Int64.repr (List.nth (bpf_ireg_to_nat i) l Z0).

Definition Z_to_int64_list (l : list Z) : list int64 :=
  map (fun i => Int64.repr i) l.

Definition bpf_interp_test
  (lp : list Z) (lm : list Z) (lc : list Z) (v : Z) (fuel : Z) (res : Z) (is_ok : bool) : bool :=
  let prog := Z_to_int64_list lp in
  let (m1, b) := Mem.alloc Mem.empty 0%Z 8590196736 in
  let m := byte_list_to_mem (Z_to_byte_list lm) m1 b 0 in
  let stk := init_stack_state in
  let sv := if Int64.eq (Int64.repr v) Int64.one then V1 else V2 in
  let st1 := bpf_interp (Z.to_nat (Z.add fuel 1%Z)) prog
                (init_bpf_state init_reg_map m (Int64.add (Int64.repr fuel) Int64.one) sv) true (Int64.repr 0x100000000%Z) b in
  if is_ok then
    match st1 with
    | BPF_Success v' => Int64.eq v' (Int64.repr res)
    | _              => false
    end
  else
    match st1 with
    | BPF_EFlag => true
    | _         => false
    end.

Definition int64_to_bpf_ireg (i : int64) : bpf_ireg :=
  match nat_to_bpf_ireg (Z.to_nat (Int64.unsigned i)) with
  | None => BR0
  | Some v => v
  end.

Definition step_test (lp : list Z) (lr : list Z) (lm : list Z) 
  (lc : list Z) (v : Z) (fuel : Z) (ipc : Z) (i : Z) (res : Z) : bool :=
  if Z.eqb res Int64.min_signed then
    true
  else
    let prog := Z_to_int64_list lp in
    let rm := reg_Map.set BR10 (Int64.add MM_STACK_START (Int64.mul stack_frame_size max_call_depth)) (Zlist_to_reg_map lr) in
    let (m1, b) := Mem.alloc Mem.empty 0%Z (Z.of_nat (List.length (Z_to_byte_list lm))) in
    let m := byte_list_to_mem (Z_to_byte_list lm) m1 b 0 in
    let stk := init_stack_state in
    let sv := if Int64.eq (Int64.repr v) Int64.one then V1 else V2 in
    let fm := init_func_map in
    match rbpf_decoder 0 prog with
    | None => false
    | Some ins0 =>
        let y : Z := 0x8000000000000000%Z in
        let st1 := step Int64.zero ins0 rm m stk sv fm true (Int64.repr 0x100000000%Z) Int64.zero (Int64.repr 3%Z) b in
        let op : int64 := decode_bpf (List.nth 0 prog Int64.zero) 0 8 in
        if orb (Int64.eq op (Int64.repr 0x18%Z)) (Nat.eqb (List.length lp) 1) then
          match st1 with
          | BPF_OK pc1 rm1 _ _ _ _ _ _ => andb (Z.eqb (Int64.signed pc1) ipc) (Z.eqb (Int64.signed (eval_reg (int64_to_bpf_ireg (Int64.repr i)) rm1)) res)
          | _ => false
          end
        else if Nat.eqb (List.length lp) 2 then
          match st1 with
          | BPF_OK pc1 rm1 m1 ss1 sv1 fm1 cur_cu1 remain_cu1 =>
              match rbpf_decoder 1 prog with
              | None => false
              | Some ins1 =>
                  let st2 := step pc1 ins1 rm1 m1 ss1 sv1 fm1 true (Int64.repr 0x100000000%Z) Int64.one (Int64.add Int64.one Int64.one) b in
                  match st2 with
                  | BPF_OK pc2 rm2 _ _ _ _ _ _ => andb (Z.eqb (Int64.signed pc2) ipc) (Z.eqb (Int64.signed (eval_reg (int64_to_bpf_ireg (Int64.repr i)) rm2)) res)
                  | _ => false
                  end
              end
          | _ => false
          end
        else
          false
    end.

(*
Print Z.gt.

Compute (Z.rem (-11%Z) (10%Z)).
Compute (Int64.mods (Int64.repr (-11)%Z) (Int64.repr 10%Z)).
Compute (modu_64_rust (Int64.repr (-11)%Z) (Int64.repr 10%Z)).
Compute (Int64.repr (-11)%Z).
Print Int64.intrange.*)
(*
Print Z.rem.
Compute (Z.rem (9802974527853709567%Z) (1624185344%Z)).
Compute (Int64.mods (Int64.repr 9802974527853709567) (Int64.repr 1624185344)).
Compute (modu_64_rust (Int64.repr 9802974527853709567) (Int64.repr 1624185344)).

Compute Int64.min_signed.
Print Z.
Print Mem.range_perm_dec.*)
