open Step_test
open Yojson.Basic.Util


(* liuhao *)
let i64_MIN = (XO (XO (XO (XO (XO (XO (XO (XO 
		(XO (XO (XO (XO (XO (XO (XO (XO 
		  (XO (XO (XO (XO (XO (XO (XO (XO 
		    (XO (XO (XO (XO (XO (XO (XO (XO 
		      (XO (XO (XO (XO (XO (XO (XO (XO 
		      	(XO (XO (XO (XO (XO (XO (XO (XO 
		      	  (XO (XO (XO (XO (XO (XO (XO (XO 
		      	    (XO (XO (XO (XO (XO (XO (XO XH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));;

let rec int64_to_positive (n : int64) : positive =
  if n = 1L then XH
  else if Stdlib.Int64.rem n 2L = 0L then XO (int64_to_positive (Stdlib.Int64.div n 2L))
  else XI (int64_to_positive (Stdlib.Int64.div n 2L))


let int64_to_z (n : int64) : z =
  if n = 0L then Z0
  else if n > 0L then Zpos (int64_to_positive n)
  else if n = 0x8000000000000000L then Zneg i64_MIN
  else Zneg (int64_to_positive (Stdlib.Int64.sub 0L n))

let int64_list_of_z_list lst =
  List.map int64_to_z lst
  
let rec positive_to_int64 (p : positive) : int64 =
  match p with
  | XH -> 1L
  | XO p' -> Stdlib.Int64.mul 2L (positive_to_int64 p')
  | XI p' -> Stdlib.Int64.add (Stdlib.Int64.mul 2L (positive_to_int64 p')) 1L   


let z_to_int64 (z : z) : int64 =
  match z with
  | Z0 -> 0L
  | Zpos p -> 
  		(*let _ = Printf.printf "p " in*)
  		positive_to_int64 p
  | Zneg p ->   (*let _ = Printf.printf "n " in*)
  		Stdlib.Int64.neg (positive_to_int64 p)


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


type test_case = {
  dis : string; 
  lp_std : int64 list;
  lr_std : int64 list;
  lm_std : int64 list;
  lc_std : int64 list;
  v : int64;
  fuel : int64;
  ipc : int64;
  index : int64;
  result_expected : int64;
}

let green = "\027[32m"  (* ANSI green *)
let red = "\027[31m"    (* ANSI red *)
let reset = "\027[0m"   (* Reset color *)
let n = ref 0
let passed = ref 0
let failed = ref 0

let merge_lp_std l =
  let rec func acc current_data index = function
    | [] -> acc
    | h::t -> 
        let new_data = Stdlib.Int64.add (Stdlib.Int64.shift_left h ((index - 1) * 8)) current_data in
        if index = 8 then
          func (acc @ [new_data]) 0L 1 t
        else
          func acc new_data (index + 1) t
  in
  func [] 0L 1 l

let run_test_case test_case =
  let v = int64_to_z test_case.v in
  let fuel = int64_to_z test_case.fuel in
  let res = int64_to_z test_case.result_expected in
  let lp1 = merge_lp_std test_case.lp_std in
  (*let _ = List.iter (fun x -> (Printf.printf "0x%Lx\n" x)) lp1 in *)
  let lp = int64_list_of_z_list lp1 in
  let lm = int64_list_of_z_list test_case.lm_std in
  let lc = int64_list_of_z_list test_case.lc_std in
  let result = bpf_interp_test lp lm lc v fuel res test_case.isok in
  let color = if result then green else red in
  if result then (
    passed := !passed + 1;
  ) else (
    failed := !failed + 1;
  );
  n := !n + 1;
  Printf.printf "%s%d %-40s result: %s%b%s\n" color !n test_case.dis color result reset


let run_test_case test_case =
  let v = int64_to_z test_case.v in
  let fuel = int64_to_z test_case.fuel in
  let index = int64_to_z test_case.index in
  let ipc = int64_to_z test_case.ipc in
  let _ = Printf.printf "%Lx\n" (z_to_int64 (Zneg i64_MIN)) in
  let _ = Printf.printf "%Ld\n" test_case.result_expected in
  let res = int64_to_z test_case.result_expected in
  let lp = int64_list_of_z_list test_case.lp_std in
  let lr = int64_list_of_z_list test_case.lr_std in
  let lm = int64_list_of_z_list test_case.lm_std in
  let lc = int64_list_of_z_list test_case.lc_std in
  (*let _ = Printf.printf "v=%Lx fuel=%Lx index=%Lx ipc=%Lx res=%Lx\n" test_case.v test_case.fuel test_case.index test_case.ipc test_case.result_expected in
  let _ = List.iter (fun x -> Printf.printf "%Lx  " x) test_case.lp_std in
  let _ = Printf.printf "\n" in
  let _ = List.iter (fun x -> Printf.printf "%Lx  " x) test_case.lr_std in
  let _ = Printf.printf "\n" in*)
  let result = step_test lp lr lm lc v fuel ipc index res in
  let color = if result then green else red in

  if result then (
    passed := !passed + 1;
  ) else (
    failed := !failed + 1;
  );
  n := !n + 1;
  Printf.printf "%s%d %-40s result: %s%b%s\n" color !n test_case.dis color result reset

let parse_test_case json =
  let dis = json |> member "dis" |> to_string in
  let lp_std = json |> member "lp_std" |> to_list |> List.map to_string in
  let lr_std = json |> member "lr_std" |> to_list |> List.map to_string in
  let lm_std = json |> member "lm_std" |> to_list |> List.map to_string in
  let lc_std = json |> member "lc_std" |> to_list |> List.map to_string in
  let v = json |> member "v" |> to_string in
  let fuel = json |> member "fuel" |> to_string in
  let index = json |> member "index" |> to_string in
  let ipc = json |> member "ipc" |> to_string in
  let result_expected = json |> member "result_expected" |> to_string in

  let parse_int64 s = Stdlib.Int64.of_string s in

  let lp_std = List.map parse_int64 lp_std in
  let lr_std = List.map parse_int64 lr_std in
  let lm_std = List.map parse_int64 lm_std in
  let lc_std = List.map parse_int64 lc_std in
  let v = parse_int64 v in
  let fuel = parse_int64 fuel in
  let index = parse_int64 index in
  let ipc = parse_int64 ipc in
  let result_expected = parse_int64 result_expected in

  { dis; lp_std; lr_std; lm_std; lc_std; v; fuel; ipc; index; result_expected }

let read_test_cases filename =
  let json = Yojson.Basic.from_file filename in
  match json with
  | `List test_cases_json -> List.map parse_test_case test_cases_json
  | _ -> failwith "Expected a list of test cases"

let () =
  let test_cases = read_test_cases "/home/liuhao/formal_solana/coq/test/ocaml_in3.json" in
  List.iter run_test_case test_cases;
  Printf.printf "\nSummary:\n";
  Printf.printf "%sPassed: %d%s\n" green !passed reset;
  Printf.printf "%sFailed: %d%s\n" red !failed reset
  

