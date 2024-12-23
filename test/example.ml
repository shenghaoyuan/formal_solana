let () =
  let v = 0x1L in
  let fuel = 0x1L in
  let index = 0x8L in
  let ipc = 0x1L in
  let res = 0xA1F9L in
  let lp = [
      0xDC,
      0x08,
      0x00,
      0x00,
      0x10,
      0x00,
      0x00,
      0x00
    ] in
  let lr = [
      0x0000000000000000L,
      0xC0444CCE72EF3F58L,
      0xFD5F65F9592DD14FL,
      0x35B9285EC845AB95L,
      0x5DCE3605F6A6D59FL,
      0x1F0419C762ED653AL,
      0x6A90F0EADEF5B3AEL,
      0xD1DB00E4B385F40BL,
      0xA58D98AF2A77F9A1L,
      0xFC8258037A81FDD3L
    ] in
  let lm = [] in
  let lc = [] in
  let result = step_test lp lr lm lc v fuel ipc index res in
  let color = if result then green else red in
  if result then (
    passed := !passed + 1;
  ) else (
    failed := !failed + 1;
  );
  n := !n + 1;
  Printf.printf "%s%d result: %s%b%s\n" color !n color result reset;
  
  Printf.printf "\nSummary:\n";
  Printf.printf "%sPassed: %d%s\n" green !passed reset;
  Printf.printf "%sFailed: %d%s\n" red !failed reset
