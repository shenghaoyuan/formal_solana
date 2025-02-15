section \<open> Interpreter of Solana rBPF \<close>

theory Interpreter
imports
  Main
  rBPFCommType rBPFSyntax vm_state vm Mem
  ebpf rBPFDecoder
begin

subsubsection  \<open> Interpreter State \<close>

record stack_state = 
call_depth :: u64
stack_pointer :: u64
call_frames :: "CallFrame list"


definition eval_reg :: "dst_ty \<Rightarrow> reg_map \<Rightarrow> u64" where
"eval_reg dst rs = rs dst"

syntax "_upd_reg" :: "'a => 'b => 'c => 'a" ("_ # _ <-- _" [1000, 1000, 1000] 1)

(* Define the translation for the notation *)
translations
  "_upd_reg a b c" => "a(b := c)"


fun create_list :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
"create_list 0 _ = []" |
"create_list (Suc n) def_v = (
  [def_v] @ (create_list n def_v)
)"

definition init_stack_state :: "stack_state" where
"init_stack_state = \<lparr> call_depth = 0, stack_pointer =
  (MM_STACK_START + (stack_frame_size * max_call_depth)),
  call_frames = create_list (unat max_call_depth)
    \<lparr> caller_saved_registers = [],
      frame_pointer = 0,
      target_pc = 0 \<rparr> \<rparr>"
(* create_list 4 0 *)

abbreviation "MM_INPUT_START :: u64 \<equiv> 0x400000000"


(*
record rbpf_state =
registers :: reg_map
memory_mapping :: mem
stack :: stack_state *)

datatype bpf_state =
  BPF_OK u64 reg_map mem stack_state SBPFV func_map u64 u64 | (**r normal state *)
  BPF_Success u64 |
  BPF_EFlag | (**r find bugs at runtime *)
  BPF_Err  (**r bad thing *)

definition init_reg_map :: "reg_map" where
"init_reg_map = (\<lambda> _. 0)"

definition init_bpf_state :: "reg_map \<Rightarrow> mem \<Rightarrow> u64 \<Rightarrow> SBPFV \<Rightarrow> bpf_state" where
"init_bpf_state rs m n v =
  BPF_OK 0
    (rs#BR10 <--
      (MM_STACK_START + (stack_frame_size * max_call_depth)))
    m init_stack_state v init_func_map 0 n"

datatype 'a option2 =
  NOK |
  OKS (the: 'a) |
  OKN  

fun eval_snd_op_i32 :: "snd_op \<Rightarrow> reg_map \<Rightarrow> i32" where
"eval_snd_op_i32 (SOImm i) _ = scast i" |
"eval_snd_op_i32 (SOReg r) rs = scast (rs r)"

fun eval_snd_op_u32 :: "snd_op \<Rightarrow> reg_map \<Rightarrow> u32" where
"eval_snd_op_u32 (SOImm i) _ = ucast i" |
"eval_snd_op_u32 (SOReg r) rs = ucast (rs r)"

fun eval_snd_op_i64 :: "snd_op \<Rightarrow> reg_map \<Rightarrow> i64" where
"eval_snd_op_i64 (SOImm i) _ = scast i" |
"eval_snd_op_i64 (SOReg r) rs = scast (rs r)"

fun eval_snd_op_u64 :: "snd_op \<Rightarrow> reg_map \<Rightarrow> u64" where
"eval_snd_op_u64 (SOImm i) _ = scast i" |
"eval_snd_op_u64 (SOReg r) rs = rs r"

subsection  \<open> ALU \<close>

definition eval_alu32_aux1 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_alu32_aux1 bop dst sop rs is_v1 = (
  let dv :: i32 = scast (eval_reg dst rs) in (
  let sv :: i32 = eval_snd_op_i32 sop rs in (
  case bop of
  BPF_ADD \<Rightarrow> OKS (rs#dst <-- (scast (dv + sv))) |
  BPF_SUB \<Rightarrow> (
    case sop of
    (SOReg i) \<Rightarrow> OKS (rs#dst <-- (scast (dv - sv))) |
    _ \<Rightarrow> (
      if is_v1 then
        OKS (rs#dst <-- (scast (dv - sv))) 
      else
        OKS (rs#dst <-- (scast (sv - dv))))) |
  BPF_MUL \<Rightarrow> OKS (rs#dst <-- (scast (dv * sv))) |
  _ \<Rightarrow> OKN
)))"

definition eval_alu32_aux2 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option2" where
"eval_alu32_aux2 bop dst sop rs = (
  let dv :: u32 = ucast (eval_reg dst rs) in (
  let sv :: u32 = eval_snd_op_u32 sop rs in (
  case bop of
  BPF_DIV \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                       else OKS (rs#dst <-- (ucast (dv div sv))) |
  BPF_OR  \<Rightarrow> OKS (rs#dst <-- (ucast (or dv sv))) |
  BPF_AND \<Rightarrow> OKS (rs#dst <-- (ucast (and dv sv))) |
  BPF_MOD \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                       else OKS (rs#dst <-- (ucast (dv mod sv))) |
  BPF_XOR \<Rightarrow> OKS (rs#dst <-- (ucast (xor dv sv))) |
  BPF_MOV \<Rightarrow> OKS (rs#dst <-- (ucast sv)) |
  BPF_LSH \<Rightarrow> OKS (rs#dst <-- (ucast (dv << unat (and sv 31)))) |
  BPF_RSH \<Rightarrow> OKS (rs#dst <-- (ucast (dv >> unat (and sv 31)))) |
  _ \<Rightarrow> OKN
)))"

definition eval_alu32_aux3 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option2" where
"eval_alu32_aux3 bop dst sop rs  = (
  let dv :: i32 = scast (eval_reg dst rs) in (
  let sv :: u32 = and (eval_snd_op_u32 sop rs) 31 in (
  case bop of
  BPF_ARSH \<Rightarrow> OKS (rs#dst <-- (and (ucast (arsh32 dv (unat sv))::u64) (ucast u32_MAX)) ) | 
  _ \<Rightarrow> OKN
)))"

definition eval_alu32 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_alu32 bop dst sop rs is_v1 = (
  case bop of
  BPF_ADD   \<Rightarrow> eval_alu32_aux1 bop dst sop rs is_v1 |
  BPF_SUB   \<Rightarrow> eval_alu32_aux1 bop dst sop rs is_v1 |
  BPF_MUL   \<Rightarrow> if is_v1 then eval_alu32_aux1 bop dst sop rs is_v1 else OKN  |
  BPF_DIV   \<Rightarrow> if is_v1 then eval_alu32_aux2 bop dst sop rs else OKN  |
  BPF_OR    \<Rightarrow> eval_alu32_aux2 bop dst sop rs  |
  BPF_AND   \<Rightarrow> eval_alu32_aux2 bop dst sop rs  |
  BPF_MOD   \<Rightarrow> if is_v1 then eval_alu32_aux2 bop dst sop rs else OKN  |
  BPF_XOR   \<Rightarrow> eval_alu32_aux2 bop dst sop rs  |
  BPF_MOV   \<Rightarrow> eval_alu32_aux2 bop dst sop rs  |
  BPF_LSH   \<Rightarrow> eval_alu32_aux2 bop dst sop rs  |
  BPF_RSH   \<Rightarrow> eval_alu32_aux2 bop dst sop rs  |
  BPF_ARSH  \<Rightarrow> eval_alu32_aux3 bop dst sop rs 
)"

definition eval_alu64_aux1 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_alu64_aux1 bop dst sop rs is_v1 = (
  let dv :: u64 = eval_reg dst rs in (
  let sv :: u64 = eval_snd_op_u64 sop rs in (
  case bop of
  BPF_ADD \<Rightarrow> OKS (rs#dst <-- (dv+sv)) |
  BPF_SUB \<Rightarrow> (case sop of (SOReg i) \<Rightarrow> OKS (rs#dst <-- (dv - sv)) |
                           _ \<Rightarrow> (if is_v1 then OKS (rs#dst <-- (dv - sv)) 
                                else OKS (rs#dst <-- (sv - dv)))) |
  BPF_MUL \<Rightarrow> OKS (rs#dst <-- (dv * sv)) |
  BPF_DIV \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                       else OKS (rs#dst <-- (dv div sv)) |
  BPF_OR  \<Rightarrow> OKS (rs#dst <-- (or dv sv)) |
  BPF_AND \<Rightarrow> OKS (rs#dst <-- (and dv sv)) |
  BPF_MOD \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                       else OKS (rs#dst <-- (dv mod sv)) |
  BPF_XOR \<Rightarrow> OKS (rs#dst <-- (xor dv sv)) |
  BPF_MOV \<Rightarrow> OKS (rs#dst <-- sv) |
  _ \<Rightarrow> OKN
)))"


definition eval_alu64_aux2 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option2" where
"eval_alu64_aux2 bop dst sop rs = (
  let dv :: u64 = eval_reg dst rs in (
  let sv :: u32 = and (eval_snd_op_u32 sop rs) 63 in (
  case bop of
  BPF_LSH \<Rightarrow> OKS (rs#dst <-- (dv << unat sv)) |  \<comment> \<open> to unat \<close>
  BPF_RSH \<Rightarrow> OKS (rs#dst <-- (dv >> unat sv)) |  \<comment> \<open> to unat \<close>
  _ \<Rightarrow> OKN
)))" 

definition eval_alu64_aux3 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option2" where
"eval_alu64_aux3 bop dst sop rs = (
  let dv :: i64 = scast (eval_reg dst rs) in (
  let sv :: u32 = and (eval_snd_op_u32 sop rs) 63 in (
  case bop of
  BPF_ARSH \<Rightarrow> OKS (rs#dst <-- (ucast (arsh64 dv (unat sv))::u64)) |
  _ \<Rightarrow> OKN
)))"

definition eval_add64_imm_R10 :: "imm_ty \<Rightarrow> stack_state \<Rightarrow> bool \<Rightarrow> stack_state option" where
"eval_add64_imm_R10 i ss is_v1 = (
  let sp = stack_pointer ss in 
    if \<not>is_v1 then
      Some (ss\<lparr>stack_pointer := sp+(scast i)\<rparr>)
    else
      None
)"

definition eval_alu64 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_alu64 bop dst sop rs is_v1 = (
  case bop of
  BPF_ADD   \<Rightarrow> eval_alu64_aux1 bop dst sop rs is_v1 |
  BPF_SUB   \<Rightarrow> eval_alu64_aux1 bop dst sop rs is_v1 |
  BPF_MUL   \<Rightarrow> if is_v1 then eval_alu64_aux1 bop dst sop rs is_v1 else OKN |
  BPF_DIV   \<Rightarrow> if is_v1 then eval_alu64_aux1 bop dst sop rs is_v1 else OKN |
  BPF_OR    \<Rightarrow> eval_alu64_aux1 bop dst sop rs is_v1 |
  BPF_AND   \<Rightarrow> eval_alu64_aux1 bop dst sop rs is_v1 |
  BPF_MOD   \<Rightarrow> if is_v1 then eval_alu64_aux1 bop dst sop rs is_v1 else OKN |
  BPF_XOR   \<Rightarrow> eval_alu64_aux1 bop dst sop rs is_v1 |
  BPF_MOV   \<Rightarrow> eval_alu64_aux1 bop dst sop rs is_v1 |
  BPF_LSH   \<Rightarrow> eval_alu64_aux2 bop dst sop rs |
  BPF_RSH   \<Rightarrow> eval_alu64_aux2 bop dst sop rs |
  BPF_ARSH  \<Rightarrow> eval_alu64_aux3 bop dst sop rs
)"

definition eval_neg32 :: "dst_ty \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_neg32 dst rs is_v1 = (if is_v1 then (let dv::i32 = scast (eval_reg dst rs) in 
    OKS ( rs#dst <-- (and (ucast(-dv)::u64) (ucast u32_MAX))) )
  else OKN
)"

definition eval_neg64 :: "dst_ty \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_neg64 dst rs is_v1 = (if is_v1 then (let dv::i64 = scast (eval_reg dst rs) in 
    OKS ( rs#dst <-- (ucast(-dv)::u64)) )
  else OKN
)"

definition eval_le :: "dst_ty \<Rightarrow> imm_ty \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_le dst imm rs is_v1 = (
  if is_v1 then (
    let dv = eval_reg dst rs in ((
      if imm = 16 then
        case (u16_of_u8_list (u8_list_of_u16 (ucast dv))) of
        None \<Rightarrow> OKN |
        Some v \<Rightarrow> OKS (rs#dst <-- (ucast v))
      else if imm = 32 then
        case u32_of_u8_list (u8_list_of_u32 (ucast dv)) of
        None \<Rightarrow> OKN |
        Some v \<Rightarrow> OKS (rs#dst <-- (ucast v))
      else if imm = 64 then
        case u64_of_u8_list (u8_list_of_u64 dv) of
        None \<Rightarrow> OKN |
        Some v \<Rightarrow> OKS (rs#dst <-- v)
      else OKN )))
  else OKN
)"

definition eval_be :: "dst_ty \<Rightarrow> imm_ty \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_be dst imm rs is_v1 = (
  if is_v1 then (
    let dv = eval_reg dst rs in ((
      if imm = 16 then
        case (u16_of_u8_list (rev (u8_list_of_u16 (ucast dv)))) of
        None \<Rightarrow> OKN |
        Some v \<Rightarrow> OKS (rs#dst <-- (ucast v))
      else if imm = 32 then
        case (u32_of_u8_list (rev (u8_list_of_u32 (ucast dv)))) of
        None \<Rightarrow> OKN |
        Some v \<Rightarrow> OKS (rs#dst <-- (ucast v))
      else if imm = 64 then
        case u64_of_u8_list (rev (u8_list_of_u64 (ucast dv))) of
        None \<Rightarrow> OKN |
        Some v \<Rightarrow> OKS (rs#dst <-- v)
      else OKN)))
  else OKN
)"

definition eval_hor64 :: "dst_ty \<Rightarrow> imm_ty \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_hor64 dst imm rs is_v1 = (
  if is_v1 then OKN
  else (
    let dv::u64 = eval_reg dst rs; dv2 = or dv (((ucast imm)::u64) << 32) in 
      OKS (rs#dst <-- dv2))
)"

subsection  \<open> PQR \<close>

definition eval_pqr32_aux1 :: "pqrop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option2" where
"eval_pqr32_aux1 pop dst sop rs  = (
  let dv :: i32 = scast (eval_reg dst rs) in (
  let sv :: i32 = eval_snd_op_i32 sop rs in (
  case pop of
  BPF_LMUL \<Rightarrow> OKS (rs#dst <-- (ucast (dv * sv))) |
  BPF_SDIV \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                        else OKS (rs#dst <-- (ucast (dv div sv))) |
  BPF_SREM \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                        else OKS (rs#dst <-- (ucast (dv mod sv))) |
  _ \<Rightarrow> OKN
)))"

definition eval_pqr32_aux2 :: "pqrop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option2" where
"eval_pqr32_aux2 pop dst sop rs = (
  let dv :: u32 = ucast (eval_reg dst rs) in (
  let sv :: u32 = eval_snd_op_u32 sop rs in (
  case pop of
  BPF_UDIV \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                        else OKS (rs#dst <-- (ucast (dv div sv))) |
  BPF_UREM \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                        else OKS (rs#dst <-- (ucast (dv mod sv))) |
  _ \<Rightarrow> OKN
)))"

definition eval_pqr32 :: "pqrop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_pqr32 pop dst sop rs is_v1 = (
  if is_v1 then OKN else(
  case pop of
  BPF_LMUL \<Rightarrow> eval_pqr32_aux1 pop dst sop rs  |
  BPF_UDIV \<Rightarrow> eval_pqr32_aux2 pop dst sop rs  | 
  BPF_UREM \<Rightarrow> eval_pqr32_aux2 pop dst sop rs  | 
  BPF_SDIV \<Rightarrow> eval_pqr32_aux1 pop dst sop rs  |
  BPF_SREM \<Rightarrow> eval_pqr32_aux1 pop dst sop rs 
))"

definition eval_pqr64_aux1 :: "pqrop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option2" where
"eval_pqr64_aux1 pop dst sop rs  = (
  let dv :: u64 = eval_reg dst rs in (
  let sv :: u64 = eval_snd_op_u64 sop rs in (
  case pop of
  BPF_LMUL \<Rightarrow> OKS (rs#dst <-- (ucast (dv * sv))) |  
  BPF_UDIV \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                        else OKS (rs#dst <-- (ucast (dv div sv))) | 
  BPF_UREM \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                        else OKS (rs#dst <-- (ucast (dv mod sv)))  |
  _ \<Rightarrow> OKN   
)))"

definition eval_pqr64_aux2 :: "pqrop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option2" where
"eval_pqr64_aux2 pop dst sop rs = (
  let dv :: i64 = scast (eval_reg dst rs) in (
  let sv :: i64 = eval_snd_op_i64 sop rs in (
  case pop of
  BPF_SDIV \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                        else OKS (rs#dst <-- (ucast (dv div sv))) | 
  BPF_SREM \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                        else OKS (rs#dst <-- (ucast (dv mod sv))) |
  _ \<Rightarrow> OKN  
)))"

definition eval_pqr64 :: "pqrop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_pqr64 pop dst sop rs is_v1 = (
  if is_v1 then OKN else(
  case pop of
  BPF_LMUL \<Rightarrow> eval_pqr64_aux1 pop dst sop rs |  
  BPF_UDIV \<Rightarrow> eval_pqr64_aux1 pop dst sop rs | 
  BPF_UREM \<Rightarrow> eval_pqr64_aux1 pop dst sop rs | 
  BPF_SDIV \<Rightarrow> eval_pqr64_aux2 pop dst sop rs | 
  BPF_SREM \<Rightarrow> eval_pqr64_aux2 pop dst sop rs
))"

definition eval_pqr64_2 :: "pqrop2 \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_pqr64_2 pop2 dst sop rs is_v1 = (
  if is_v1 then OKN else(
  let dv_u :: u128 = ucast (eval_reg dst rs) in (
  let sv_u :: u128 = ucast (eval_snd_op_u64 sop rs) in (
  let dv_i :: u128 = ucast (scast (eval_reg dst rs)::i64) in (
  let sv_i :: u128 = ucast (scast (eval_reg dst rs)::i64) in (
  case pop2 of
  BPF_UHMUL \<Rightarrow> OKS (rs#dst <-- (ucast (dv_u * sv_u)>>64)) |
  BPF_SHMUL \<Rightarrow> OKS (rs#dst <-- (ucast (dv_i * sv_i)>>64)) 
))))))"

subsection  \<open> MEM \<close>

definition eval_store :: "memory_chunk \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> off_ty \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> mem option" where
"eval_store chk dst sop off rs mem = (
  let dv :: i64 = scast (eval_reg dst rs) in (
  let vm_addr :: u64 = ucast (dv + (scast off)) in (  
  let sv :: u64 = eval_snd_op_u64 sop rs in ( \<comment> \<open> TODO: sv is signed for imm and unsigned for src reg? \<close>
  (storev chk mem vm_addr (memory_chunk_value_of_u64 chk sv))
))))"


definition eval_load :: "memory_chunk \<Rightarrow> dst_ty \<Rightarrow> src_ty \<Rightarrow> off_ty \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> reg_map option" where
"eval_load chk dst sop off rs mem = (
  let sv :: u64 = eval_snd_op_u64 (SOReg sop) rs in (
  let vm_addr :: u64 = sv + (scast off) in (  
  let v = loadv chk mem vm_addr in (
    case v of 
    None \<Rightarrow> None |
    Some Vundef \<Rightarrow>  None | 
    Some (Vlong v) \<Rightarrow>  Some (rs#dst <-- v) |
    Some (Vint v) \<Rightarrow> Some (rs#dst <-- (ucast v)) |
    Some (Vshort v) \<Rightarrow> Some (rs#dst <-- (ucast v)) |
    Some (Vbyte v) \<Rightarrow> Some (rs#dst <-- (ucast v))
))))"

definition eval_load_imm :: "dst_ty \<Rightarrow> imm_ty \<Rightarrow> imm_ty \<Rightarrow> reg_map \<Rightarrow> reg_map" where
"eval_load_imm dst imm1 imm2 rs = (
  let v :: u64 = or (and (ucast imm1) 0xffffffff) ((ucast imm2) << 32) in
    (rs#dst <-- v)
)"


subsection  \<open> JUMP \<close>

definition eval_jmp :: "condition \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool" where
"eval_jmp cond dst sop rs = (
  let udv :: u64 = eval_reg dst rs in (
  let usv :: u64 = eval_snd_op_u64 sop rs in (
  let sdv :: i64 = scast udv in (
  let ssv :: i64 = eval_snd_op_i64 sop rs in (
  case cond of
  Eq  \<Rightarrow> udv = usv |
  Gt  \<Rightarrow> udv > usv |
  Ge  \<Rightarrow> udv \<ge> usv |
  Lt  \<Rightarrow> udv < usv |
  Le  \<Rightarrow> udv \<le> usv |
  SEt \<Rightarrow> and udv usv\<noteq>0 |
  Ne  \<Rightarrow> udv \<noteq> usv |
  SGt \<Rightarrow> ssv <s sdv |
  SGe \<Rightarrow> ssv \<le>s sdv |
  SLt \<Rightarrow> sdv <s ssv |
  SLe \<Rightarrow> sdv \<le>s ssv ))))
)"

subsection  \<open> CALL \<close>

definition push_frame:: "reg_map \<Rightarrow> stack_state \<Rightarrow> bool \<Rightarrow> u64 \<Rightarrow> bool \<Rightarrow> stack_state option \<times> reg_map" where 
"push_frame rs ss is_v1 pc enable_stack_frame_gaps = (
  let npc = pc +1 in
  let fp = eval_reg BR10 rs in
  let caller = [eval_reg BR6 rs, eval_reg BR7 rs,
                eval_reg BR8 rs, eval_reg BR9 rs] in
  let frame = \<lparr> caller_saved_registers = caller,
                frame_pointer = fp, target_pc = npc\<rparr> in 
  let update1 = call_depth ss +1 in (
    if update1 = max_call_depth then (None, rs)
    else (
      let update2 =
        if is_v1 then (
          if enable_stack_frame_gaps then
            stack_pointer ss + stack_frame_size *2
          else
            stack_pointer ss + stack_frame_size)
        else
          stack_pointer ss;  
        update3 = (call_frames ss)[unat(call_depth ss):= frame] in
      let stack = Some \<lparr> call_depth = update1, stack_pointer = update2,
        call_frames = update3\<rparr>;
        reg = rs#BR10 <-- update2 in
          (stack, reg)
)))"

definition eval_call_reg :: "src_ty \<Rightarrow> imm_ty \<Rightarrow> reg_map \<Rightarrow> stack_state \<Rightarrow> bool \<Rightarrow> u64 \<Rightarrow>
  func_map \<Rightarrow> bool \<Rightarrow> u64 \<Rightarrow> (u64 \<times> reg_map \<times> stack_state) option" where
"eval_call_reg src imm rs ss is_v1 pc fm enable_stack_frame_gaps program_vm_addr = (
  case u4_to_bpf_ireg (ucast imm) of
  None \<Rightarrow> None |
  Some iv \<Rightarrow> (
    let pc1 = if is_v1 then eval_reg iv rs else eval_reg src rs in  
    let (x, rs') = push_frame rs ss is_v1 pc enable_stack_frame_gaps in
      case x of
      None \<Rightarrow> None |
      Some ss' \<Rightarrow> 
        if pc1 < program_vm_addr then None else (
          let next_pc = (pc1 - program_vm_addr)div (of_nat INSN_SIZE) in 
            Some (next_pc, rs', ss')
          ))
)"

definition eval_call_imm :: "u64 \<Rightarrow> src_ty \<Rightarrow> imm_ty \<Rightarrow> reg_map \<Rightarrow> stack_state \<Rightarrow> bool \<Rightarrow> func_map \<Rightarrow> bool \<Rightarrow> (u64 \<times> reg_map \<times> stack_state) option" where
"eval_call_imm pc src imm rs ss is_v1 fm enable_stack_frame_gaps = (
  let pc_option =
    if src = BR0 then
      get_function_registry (ucast imm) fm
    else
      Some (ucast imm) in
  case pc_option of
  None \<Rightarrow> None |
  Some npc \<Rightarrow> (
    let (x, rs') = push_frame rs ss is_v1 pc enable_stack_frame_gaps in (
      case x of
      None \<Rightarrow> None |
      Some ss' \<Rightarrow> Some (npc, rs', ss')
    ))
)"

definition pop_frame:: "stack_state \<Rightarrow> CallFrame" where 
"pop_frame ss = (call_frames ss)!(unat (call_depth ss - 1)) "

subsection  \<open> EXIT \<close>
                                       
definition eval_exit :: "reg_map \<Rightarrow> stack_state \<Rightarrow> bool \<Rightarrow> (u64 \<times> reg_map \<times> stack_state)" where
"eval_exit rs ss is_v1 = (
  let x = call_depth ss-1 in
  let frame = pop_frame ss in
  let rs'= (((((
            rs#BR10 <-- (frame_pointer frame))
              #BR9  <-- ((caller_saved_registers frame)!(3)))
              #BR8  <-- ((caller_saved_registers frame)!(2)))
              #BR7  <-- ((caller_saved_registers frame)!(1)))
              #BR6  <-- ((caller_saved_registers frame)!(0))) in 
  let y =
    if is_v1 then
      (stack_pointer ss - (2 * stack_frame_size))
    else
      stack_pointer ss in 
  let z = butlast (call_frames ss) in
  let ss' = \<lparr>call_depth = x, stack_pointer= y, call_frames = z\<rparr> in
  let pc = target_pc frame in 
    (pc, rs', ss')
)"

subsection  \<open> step \<close>

fun step :: "u64 \<Rightarrow> bpf_instruction \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> stack_state \<Rightarrow> SBPFV \<Rightarrow>
  func_map \<Rightarrow> bool \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> bpf_state" where
"step pc ins rs m ss sv fm enable_stack_frame_gaps program_vm_addr cur_cu remain_cu = (
  let is_v1 = (case sv of V1 \<Rightarrow> True | _ \<Rightarrow> False) in
  case ins of
  BPF_ALU bop d sop \<Rightarrow> (
    case eval_alu32 bop d sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv fm (cur_cu+1) remain_cu ) |
  BPF_ALU64 bop d sop \<Rightarrow> (
    case eval_alu64 bop d sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv fm (cur_cu+1) remain_cu ) |
  BPF_ADD_STK i \<Rightarrow> (
    case eval_add64_imm_R10 i ss is_v1 of
    None \<Rightarrow> BPF_Err |
    Some ss' \<Rightarrow> BPF_OK (pc+1) rs m ss' sv fm (cur_cu+1) remain_cu ) |
  BPF_LE dst imm \<Rightarrow> (
    case eval_le dst imm rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv fm (cur_cu+1) remain_cu ) |
  BPF_BE dst imm \<Rightarrow> (
    case eval_be dst imm rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv fm (cur_cu+1) remain_cu ) |
  BPF_NEG32_REG dst \<Rightarrow> (
    case eval_neg32 dst rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv fm (cur_cu+1) remain_cu ) |
  BPF_NEG64_REG dst \<Rightarrow> (
    case eval_neg64 dst rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv fm (cur_cu+1) remain_cu ) | 
  BPF_LDX chk dst sop off \<Rightarrow> (
    case eval_load chk dst sop off rs m of
    None \<Rightarrow> BPF_EFlag |
    Some rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv fm (cur_cu+1) remain_cu ) |
  BPF_ST chk dst sop off \<Rightarrow> (
    case eval_store chk dst sop off rs m of
    None \<Rightarrow> BPF_EFlag |
    Some m' \<Rightarrow> BPF_OK (pc+1) rs m' ss sv fm (cur_cu+1) remain_cu) |
  BPF_LD_IMM dst imm1 imm2  \<Rightarrow> (
    let rs' = eval_load_imm dst imm1 imm2 rs in
      BPF_OK (pc+2) rs' m ss sv fm (cur_cu+1) remain_cu) |
  BPF_PQR pop dst sop \<Rightarrow> (
    case eval_pqr32 pop dst sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv fm (cur_cu+1) remain_cu ) |
  BPF_PQR64 pop dst sop \<Rightarrow> (
    case eval_pqr64 pop dst sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv fm (cur_cu+1) remain_cu ) |
  BPF_PQR2 pop dst sop \<Rightarrow> (
    case eval_pqr64_2 pop dst sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv fm (cur_cu+1) remain_cu ) |
  BPF_HOR64_IMM dst imm \<Rightarrow> (
    case eval_hor64 dst imm rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv fm (cur_cu+1) remain_cu) |

  BPF_JA off  \<Rightarrow>
    BPF_OK (pc + scast off + 1) rs m ss sv fm (cur_cu+1) remain_cu |

  BPF_JUMP cond bpf_ireg snd_op off  \<Rightarrow> (
    if eval_jmp cond bpf_ireg snd_op rs  then
      BPF_OK (pc + scast off + 1) rs m ss sv fm (cur_cu+1) remain_cu
    else
      BPF_OK (pc + 1) rs m ss sv fm (cur_cu+1) remain_cu) |
  BPF_CALL_IMM src imm \<Rightarrow> (
    case eval_call_imm pc src imm rs ss is_v1 fm enable_stack_frame_gaps of
    None \<Rightarrow> BPF_EFlag |
    Some (pc, rs', ss') \<Rightarrow> BPF_OK pc rs' m ss' sv fm (cur_cu+1) remain_cu ) |
  BPF_CALL_REG src imm \<Rightarrow> (
    case eval_call_reg src imm rs ss is_v1 pc fm enable_stack_frame_gaps program_vm_addr of
    None \<Rightarrow> BPF_EFlag |
    Some (pc', rs', ss') \<Rightarrow> BPF_OK pc' rs' m ss' sv fm (cur_cu+1) remain_cu ) |
  BPF_EXIT \<Rightarrow> (
    if call_depth ss = 0 then
      if cur_cu >  remain_cu then
        BPF_EFlag
      else
        BPF_Success (rs BR0)
    else (
      let (pc', rs', ss') = eval_exit rs ss is_v1 in
        BPF_OK pc' rs' m ss' sv fm (cur_cu+1) remain_cu)) 
)"

fun bpf_interp :: "nat \<Rightarrow> bpf_bin \<Rightarrow> bpf_state \<Rightarrow> bool \<Rightarrow> u64 \<Rightarrow> bpf_state" where
"bpf_interp 0 _ _ _ _ = BPF_EFlag" | 
"bpf_interp (Suc n) prog st enable_stack_frame_gaps program_vm_addr = (
  case st of
  BPF_EFlag \<Rightarrow> BPF_EFlag |
  BPF_Err \<Rightarrow> BPF_Err |
  BPF_Success v \<Rightarrow> BPF_Success v |
  BPF_OK pc rs m ss sv fm cur_cu remain_cu \<Rightarrow> (
    if INSN_SIZE*unat pc < length prog then
      if cur_cu \<ge> remain_cu then
        BPF_EFlag
      else
        case bpf_find_instr (unat pc) prog of
        None \<Rightarrow> BPF_EFlag |
        Some ins \<Rightarrow>
          let st1 = step pc ins rs m ss sv fm enable_stack_frame_gaps program_vm_addr cur_cu remain_cu in 
          bpf_interp n prog st1
            enable_stack_frame_gaps program_vm_addr
    else BPF_EFlag))"

definition int_to_u8_list :: "int list \<Rightarrow> u8 list" where
"int_to_u8_list lp = (map (\<lambda>i. of_int i) lp)"


(**r the initial state of R1 should be MM_INPUT_START, so here should be (MM_INPUT_START + i), we set MM_INPUT_START = 0 in this model *)
definition u8_list_to_mem :: "u8 list \<Rightarrow> mem" where
"u8_list_to_mem l = (\<lambda> i. if (unat i) < length(l) then Some (l!((unat i))) else None)"

definition intlist_to_reg_map :: "int list \<Rightarrow> reg_map" where
" intlist_to_reg_map l = ( \<lambda> r.
    case r of BR0 \<Rightarrow> of_int (l!0) |
              BR1 \<Rightarrow> of_int (l!1) |
              BR2 \<Rightarrow> of_int (l!2) |
              BR3 \<Rightarrow> of_int (l!3) |
              BR4 \<Rightarrow> of_int (l!4) |
              BR5 \<Rightarrow> of_int (l!5) |
              BR6 \<Rightarrow> of_int (l!6) |
              BR7 \<Rightarrow> of_int (l!7) |
              BR8 \<Rightarrow> of_int (l!8) |
              BR9 \<Rightarrow> of_int (l!9) |
              BR10\<Rightarrow> of_int (l!10)
)"

definition bpf_interp_test ::
  "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool \<Rightarrow> bool" where
"bpf_interp_test lp lm lc v fuel res is_ok = (
  let st1 = bpf_interp (nat (fuel+1)) (int_to_u8_list lp)
    (init_bpf_state init_reg_map (u8_list_to_mem (int_to_u8_list lm) )
      (of_int (fuel+1)) (if v = 1 then V1 else V2)) True 0x100000000 in
    if is_ok then (
      case st1 of
      BPF_Success v \<Rightarrow> v = of_int res |
      _ \<Rightarrow> False )
    else (
      case st1 of
      BPF_EFlag \<Rightarrow> True |
      _ \<Rightarrow> False)
)"
definition int_to_bpf_ireg :: "int \<Rightarrow> bpf_ireg" where
"int_to_bpf_ireg i = (
  case u4_to_bpf_ireg (of_int i) of
  None \<Rightarrow> BR0 |
  Some v \<Rightarrow> v
)"

(*
definition u8_list_to_mem_plus :: "u8 list \<Rightarrow> mem" where
"u8_list_to_mem_plus l = (\<lambda> i.
  if (unat i) < 0x400000000 then
    None
  else if (unat i) - 0x400000000 < length(l) then
    Some (l!(unat i))
  else
    None)" *)

definition step_test ::
  "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
"step_test lp lr lm lc v fuel ipc i res = (
  if of_int res = i64_MIN then True else 
  let prog  = int_to_u8_list lp in
  let rs    = ((intlist_to_reg_map lr)#BR10 <--
      (MM_STACK_START + (stack_frame_size * max_call_depth))) in
  let m     = u8_list_to_mem (int_to_u8_list lm) in
  let stk   = init_stack_state in
  let sv    = if v = 1 then V1 else V2 in
  let fm    = init_func_map in (
    case bpf_find_instr 0 prog of
    None \<Rightarrow> False |
    Some ins0 \<Rightarrow> 
      let st1 = step 0 ins0 rs m stk sv fm True 0x100000000 0 3 in
        if prog!(0) = 0x18 \<or> length lp = 8 then ( \<comment> \<open> for ALU,branch, memory load \<close>
          case st1 of
          BPF_OK pc1 rs1 _ _ _ _ _ _ \<Rightarrow> (pc1 = of_int ipc) \<and> (rs1 (int_to_bpf_ireg i) = of_int res) |
          _ \<Rightarrow> False )
        else if length lp = 16 then ( \<comment> \<open> for memory store \<close>
          case st1 of
          BPF_OK pc1 rs1 m1 ss1 sv1 fm1 cur_cu1 remain_cu1 \<Rightarrow> (
            case bpf_find_instr 1 prog of
            None \<Rightarrow> False |
            Some ins1 \<Rightarrow> (
              case step pc1 ins1 rs1 m1 ss1 sv1 fm1 True 0x100000000 1 2 of
              BPF_OK pc2 rs2 _ _ _ _ _ _ \<Rightarrow> (pc2 = of_int ipc) \<and> (rs2 (int_to_bpf_ireg i) = of_int res) |
              _ \<Rightarrow> False ) ) |
          _ \<Rightarrow> False )
        else False )
)"

(*
definition step_test1 ::
  "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> (u64 * u64) option" where
"step_test1 lp lr lm lc v fuel ipc i = (
  let prog  = int_to_u8_list lp in
  let rs    = ((intlist_to_reg_map lr)#BR10 <--
      (MM_STACK_START + (stack_frame_size * max_call_depth))) in
  let m     = u8_list_to_mem (int_to_u8_list lm) in
  let stk   = init_stack_state in
  let sv    = if v = 1 then V1 else V2 in
  let fm    = init_func_map in (
    case bpf_find_instr 0 prog of
    None \<Rightarrow> None |
    Some ins0 \<Rightarrow> 
      let st1 = step 0 ins0 rs m stk sv fm True 0x100000000 0 3 in
        if prog!(0) = 0x18 \<or> length lp = 8 then ( \<comment> \<open> for ALU,branch, memory load \<close>
          case st1 of
          BPF_OK pc1 rs1 _ _ _ _ _ _ \<Rightarrow> Some (pc1, rs1 (int_to_bpf_ireg i)) |
          _ \<Rightarrow> None )
        else if length lp = 16 then ( \<comment> \<open> for memory store \<close>
          case st1 of
          BPF_OK pc1 rs1 m1 ss1 sv1 fm1 cur_cu1 remain_cu1 \<Rightarrow> (
            case bpf_find_instr 1 prog of
            None \<Rightarrow> None |
            Some ins1 \<Rightarrow> (
              case step pc1 ins1 rs1 m1 ss1 sv1 fm1 True 0x100000000 1 2 of
              BPF_OK pc2 rs2 _ _ _ _ _ _ \<Rightarrow> Some (pc2, rs2 (int_to_bpf_ireg i)) |
              _ \<Rightarrow> None ) ) |
          _ \<Rightarrow> None )
        else None )
)"
value "step_test1
  [ 0x18, 0x00, 0x00, 0x00, 0x12, 0x34, 0x56, 0x78,
    0x00, 0x00, 0x00, 0x00, 0x9a, 0xbc, 0xde, 0xf0]
  [ 0x0000000000000000, 0xB93C732C3C25264D, 0x7BED36F9786AA8FF, 0x23A0682F7E883EB9,
    0x343330A3A66902F7, 0x0D74ED1EBAD8DF8E, 0x5012F6BEC353AAC1, 0x4509C87940AB1BDE,
    0x9C443012D4B72741, 0xB5D25DFEA9184088]
  []
  [] 2 2 2 0" *)

(*
value "step_test
  [ 0x63, 0x90, 0x34, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x79, 0x08, 0x34, 0x00, 0x00, 0x00, 0x00, 0x00]
  [ 0x0000000000000000, 0xB93C732C3C25264D, 0x7BED36F9786AA8FF, 0x23A0682F7E883EB9,
    0x343330A3A66902F7, 0x0D74ED1EBAD8DF8E, 0x5012F6BEC353AAC1, 0x4509C87940AB1BDE,
    0x9C443012D4B72741, 0xB5D25DFEA9184088]
  [ 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A,
    0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15,
    0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20,
    0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2A, 0x2B,
    0x2C, 0x2D, 0x2E, 0x2F, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,
    0x37, 0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40, 0x41,
    0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C,
    0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57,
    0x58, 0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60, 0x61, 0x62,
    0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D]
  [] 2 2 2 8 0x3B3A3938A9184088"

*)

(*
value "(of_int (-8613303245920329199::int)::u64)"

value "bpf_interp_test
  [191, 16, 0, 0, 0, 0, 0, 0, 106, 0, 0, 0, 52, 18, 0, 0, 105, 0, 0, 0, 0, 0, 0, 0, 149, 0, 0, 0, 0, 0, 0, 0]
  [0xff, 0xff]
  []
  2 4 0x1234" *)
(*
value "let l :: u32 list = [1] in l[0 := 2]" *)

(*
value "bpf_interp_test
  [ 183, 0, 0, 0, 0, 0, 0, 0,
    183, 8, 0, 0, 1, 0, 0, 0,
    103, 8, 0, 0, 32, 0, 0, 0,
    71, 8, 0, 0, 48, 0, 0, 0,
    141, 128, 0, 0, 0, 0, 0, 0,
    149, 0, 0, 0, 0, 0, 0, 0,
    183, 0, 0, 0, 42, 0, 0, 0,
    149, 0, 0, 0, 0, 0, 0, 0]
  [] []
  2 8
  0x2a" *)

(*
value "bpf_interp_test
  [ 0xb7, 0x06, 0x00, 0x00, 0x11, 0x00, 0x00, 0x00,
    0xb7, 0x07, 0x00, 0x00, 0x22, 0x00, 0x00, 0x00,
    0xb7, 0x08, 0x00, 0x00, 0x44, 0x00, 0x00, 0x00,
    0xb7, 0x09, 0x00, 0x00, 0x88, 0x00, 0x00, 0x00,
    0x85, 0x10, 0x00, 0x00, 0x0a, 0x00, 0x00, 0x00,
    0xbf, 0x60, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x0f, 0x70, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x0f, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x0f, 0x90, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0xb7, 0x06, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0xb7, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0xb7, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0xb7, 0x09, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  [] []
  2 15
  0xff" *)

(*
value "(and (4::u32) 63)"
value "(2::u64) << (unat (and (4::u32) 63))"

value "bpf_interp_test
  [ 0xb4, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0xb7, 0x01, 0x00, 0x00, 0xfe, 0xff, 0xff, 0xff, 
    0x75, 0x01, 0x05, 0x00, 0xff, 0xff, 0xff, 0xff, 
    0x75, 0x01, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 
    0xb4, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 
    0xb7, 0x01, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 
    0x75, 0x01, 0x01, 0x00, 0xff, 0xff, 0xff, 0xff, 
    0xb4, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 
    0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09]
  []
  2 8 0x1"

value "loadv M8 (u8_list_to_mem (int_to_u8_list [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09])) 2" *)

(*
value "loadv M16 (u8_list_to_mem (int_to_u8_list [0x11, 0x22, 0x33])) 1"
(**r return 0x3322 = 13090 *)
value "(u16_of_u8_list (rev (u8_list_of_u16 (ucast (0x3322::u64)))))"
(**r return 0x2233 = 8755 *)
value "case storev M16 init_mem 0 (Vshort 0x1122) of None \<Rightarrow> None | Some m \<Rightarrow> loadv M16 m 0"
(**r return 0x1122 =4386 *)
*)
end