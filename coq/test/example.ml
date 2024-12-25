open Step_test



let () =
  let v = int64_to_z 0x1L in
  let fuel = int64_to_z 0x1L in
  let index = int64_to_z 0x8L in
  let ipc = int64_to_z 0x1L in
  let res = int64_to_z 0xA1F9L in
  let lp = int64_list_of_z_list [
      0x00000010000008DCL;
    ] in
  let lr = int64_list_of_z_list [
      0x0000000000000000L;
      0xC0444CCE72EF3F58L;
      0xFD5F65F9592DD14FL;
      0x35B9285EC845AB95L;
      0x5DCE3605F6A6D59FL;
      0x1F0419C762ED653AL;
      0x6A90F0EADEF5B3AEL;
      0xD1DB00E4B385F40BL;
      0xA58D98AF2A77F9A1L;
      0xFC8258037A81FDD3L
    ] in
  let lm = [] in
  let lc = [] in
  let result = step_test lp lr lm lc v fuel ipc index res in
 (* let color = if result then green else red in
  if result then (
    passed := !passed + 1;
  ) else (
    failed := !failed + 1;
  );
  n := !n + 1;*)
  Printf.printf "result: %b\n"  result;
  Printf.printf "expection: %Lx\n" (z_to_int64 res)
  
  (* liuhao 
let rec int64_to_positive (n : int64) : positive =
  if n = 0L then XH
  else
    let rest = Stdlib.Int64.div n 2L in
    let bit = Stdlib.Int64.rem n 2L in
    match bit with
    | 0L -> XO (int64_to_positive rest)
    | 1L -> XI (int64_to_positive rest)
    | _ -> assert false


let int64_to_z (n : int64) : z =
  if n = 0L then Z0
  else if n > 0L then Zpos (int64_to_positive n)
  else Zneg (int64_to_positive (Stdlib.Int64.neg n))

let int64_list_of_z_list lst =
  List.map int64_to_z lst
  
let rec positive_to_int64 (p : positive) : int64 =
  match p with
  | XH -> 0L
  | XO p' -> Stdlib.Int64.mul 2L (positive_to_int64 p')
  | XI p' -> Stdlib.Int64.add (Stdlib.Int64.mul 2L (positive_to_int64 p')) 1L   


let z_to_int64 (z : z) : int64 =
  match z with
  | Z0 -> 0L
  | Zpos p -> positive_to_int64 p
  | Zneg p -> Stdlib.Int64.neg (positive_to_int64 p)
  
  
  
let print_regmap rs =
  let reg_list = [("R0", BR0); ("R1", BR1); ("R2", BR2); ("R3", BR3);
                  ("R4", BR4); ("R5", BR5); ("R6", BR6); ("R7", BR7);
                  ("R8", BR8); ("R9", BR9); ("R10", BR10)] in
  List.iter (fun (name, reg) ->
    Printf.printf "%s: %Lx\n" name (z_to_int64 (eval_reg reg rs))
  ) reg_list

let print_bpf_state st =
  match st with
    BPF_OK (pc, rs, m, ss, sv, fm, cur_cu, remain_cu) -> 
    let _ = print_regmap rs in
      Printf.printf "PC: %Lx\n" (z_to_int64 pc)
  | BPF_Success _ -> print_endline("success")
  | _ -> print_endline("error")
  
  
  
  
(* liuhao *)
let rec int64_to_positive (n : int64) : positive =
  if n = 0L then XH
  else
    let rest = Stdlib.Int64.div n 2L in
    let bit = Stdlib.Int64.rem n 2L in
    match bit with
    | 0L -> XO (int64_to_positive rest)
    | 1L -> XI (int64_to_positive rest)
    | _ -> assert false


let int64_to_z (n : int64) : z =
  if n = 0L then Z0
  else if n > 0L then Zpos (int64_to_positive n)
  else Zneg (int64_to_positive (Stdlib.Int64.neg n))

let int64_list_of_z_list lst =
  List.map int64_to_z lst
  
let rec positive_to_int64 (p : positive) : int64 =
  match p with
  | XH -> 0L
  | XO p' -> Stdlib.Int64.mul 2L (positive_to_int64 p')
  | XI p' -> Stdlib.Int64.add (Stdlib.Int64.mul 2L (positive_to_int64 p')) 1L   


let z_to_int64 (z : z) : int64 =
  match z with
  | Z0 -> 0L
  | Zpos p -> positive_to_int64 p
  | Zneg p -> Stdlib.Int64.neg (positive_to_int64 p)
  *)
