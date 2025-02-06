open Yojson.Basic

let merge_lp_std l =
  let rec func acc current_string = function
    | [] -> acc
    | h::t -> 
        let new_string = [String.sub h 2 2] @ current_string in
        if List.length new_string = 8 then
          func (acc @ ["0x" ^ String.concat "" new_string]) [] t
        else
          func acc new_string t
  in
  func [] [] l


let modify_json_lp json =
  match json with
  | `List items ->
      let updated_items = List.map (fun item ->
          match item with
          | `Assoc fields ->
              let updated_fields = List.map (fun (key, value) ->
                  if key = "lp_std" then 
                    match value with
                    | `List lp_std_list ->
                        let string_list = List.map (function
                          | `String s -> s
                          | _ -> failwith "Expected a string in lp_std") lp_std_list in
                        let new_lp = merge_lp_std string_list in
                        ("lp_std", `List (List.map (fun x -> `String x) new_lp))
                    | _ -> (key, value)
                  else
                    (key, value)
                ) fields
              in
              `Assoc updated_fields
          | _ -> item
        ) items
      in
      `List updated_items
  | _ -> json


let modify_file filename =
  let json = Yojson.Basic.from_file filename in
  let updated_json = modify_json_lp json in
  Yojson.Basic.to_file "ocaml_in1.json" updated_json


let () =
  modify_file "ocaml_in.json"

