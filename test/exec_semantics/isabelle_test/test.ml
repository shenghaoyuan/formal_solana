open Interp_test

type test_case = {
  dis : string; 
  lp_std : int64 list;
  lm_std : int64 list;
  lc_std : int64 list;
  v : int64;
  fuel : int64;
  result_expected : int64;
  isok : bool;
}

let green = "\027[32m"  (* ANSI green *)
let red = "\027[31m"    (* ANSI red *)
let reset = "\027[0m"   (* Reset color *)
let n = ref 0
let passed = ref 0
let failed = ref 0

let run_test_case test_case =
  let v = Interp_test.int_of_standard_int test_case.v in
  let fuel = Interp_test.int_of_standard_int test_case.fuel in
  let res = Interp_test.int_of_standard_int test_case.result_expected in
  let lp = Interp_test.int_list_of_standard_int_list test_case.lp_std in
  let lm = Interp_test.int_list_of_standard_int_list test_case.lm_std in
  let lc = Interp_test.int_list_of_standard_int_list test_case.lc_std in
  let result = Interp_test.bpf_interp_test lp lm lc v fuel res test_case.isok in
  let color = if result then green else red in
  if result then (
    passed := !passed + 1;
  ) else (
    failed := !failed + 1;
  );
  n := !n + 1;
  Printf.printf "%s%d %-40s result: %s%b%s\n" color !n test_case.dis color result reset
  
let test_cases = [
  (*
    mov32 r1, 1
    mov32 r0, r1
    exit*)
  {
    dis = "test_mov";
    lp_std = [180L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 188L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 3L;
    result_expected = 0x01L;
  };
  (*
    mov32 r0, -1
    exit*)
  {
    dis = "test_mov32_imm_large";
    lp_std = [180L; 0L; 0L; 0L; 255L; 255L; 255L; 255L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 2L;
    result_expected = 0xffffffffL;
  };
  (*
    mov32 r1, -1
    mov32 r0, r1
    exit*)
  {
    dis = "test_mov_large";
    lp_std = [180L; 1L; 0L; 0L; 255L; 255L; 255L; 255L; 188L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 3L;
    result_expected = 0xffffffffL;
  };
  (*
    mov r0, 1
    mov r6, r0
    mov r7, r6
    mov r8, r7
    mov r9, r8
    mov r0, r9
    exit*)
  {
    dis = "test_bounce";
    lp_std = [183L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 191L; 6L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 103L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 120L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 137L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 144L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 7L;
    result_expected = 0x01L;
  };
  (*
    mov32 r0, 0L
    mov32 r1, 2
    add32 r0, 1
    add32 r0, r1
    exit*)
    {
      dis = "test_add32";
      lp_std = [180L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 180L; 1L; 0L; 0L; 2L; 0L; 0L; 0L; 4L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 12L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
      lm_std = [];
      lc_std = [];
    isok = true;
      v = 2L;
      fuel = 5L;
      result_expected = 0x3L;
    };
  (*
    mov32 r0, 0
    mov32 r1, 1
    mov32 r2, 2
    mov32 r3, 3
    mov32 r4, 4
    mov32 r5, 5
    mov32 r6, 6
    mov32 r7, 7
    mov32 r8, 8
    mov32 r9, 9
    sub32 r0, 13
    sub32 r0, r1
    add32 r0, 23
    add32 r0, r7
    lmul32 r0, 7
    lmul32 r0, r3
    udiv32 r0, 2
    udiv32 r0, r4
    exit*)
    {
      dis = "test_alu32_arithmetic";
      lp_std = [180L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 180L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 180L; 2L; 0L; 0L; 2L; 0L; 0L; 0L; 180L; 3L; 0L; 0L; 3L; 0L; 0L; 0L; 180L; 4L; 0L; 0L; 4L; 0L; 0L; 0L; 180L; 5L; 0L; 0L; 5L; 0L; 0L; 0L; 180L; 6L; 0L; 0L; 6L; 0L; 0L; 0L; 180L; 7L; 0L; 0L; 7L; 0L; 0L; 0L; 180L; 8L; 0L; 0L; 8L; 0L; 0L; 0L; 180L; 9L; 0L; 0L; 9L; 0L; 0L; 0L; 20L; 0L; 0L; 0L; 13L; 0L; 0L; 0L; 28L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 4L; 0L; 0L; 0L; 23L; 0L; 0L; 0L; 12L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 134L; 0L; 0L; 0L; 7L; 0L; 0L; 0L; 142L; 48L; 0L; 0L; 0L; 0L; 0L; 0L; 70L; 0L; 0L; 0L; 2L; 0L; 0L; 0L; 78L; 64L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
      lm_std = [];
      lc_std = [];
    isok = true;
      v = 2L;
      fuel = 19L;
      result_expected = 110L;
    };  
  (*
    mov r0, 0
    mov r1, 1
    mov r2, 2
    mov r3, 3
    mov r4, 4
    mov r5, 5
    mov r6, 6
    mov r7, 7
    mov r8, 8
    mov r9, 9
    sub r0, 13
    sub r0, r1
    add r0, 23
    add r0, r7
    lmul r0, 7
    lmul r0, r3
    udiv r0, 2
    udiv r0, r4
    exit*)
    {
      dis = "test_alu64_arithmetic";
      lp_std = [183L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 183L; 2L; 0L; 0L; 2L; 0L; 0L; 0L; 183L; 3L; 0L; 0L; 3L; 0L; 0L; 0L; 183L; 4L; 0L; 0L; 4L; 0L; 0L; 0L; 183L; 5L; 0L; 0L; 5L; 0L; 0L; 0L; 183L; 6L; 0L; 0L; 6L; 0L; 0L; 0L; 183L; 7L; 0L; 0L; 7L; 0L; 0L; 0L; 183L; 8L; 0L; 0L; 8L; 0L; 0L; 0L; 183L; 9L; 0L; 0L; 9L; 0L; 0L; 0L; 23L; 0L; 0L; 0L; 13L; 0L; 0L; 0L; 31L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 7L; 0L; 0L; 0L; 23L; 0L; 0L; 0L; 15L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 150L; 0L; 0L; 0L; 7L; 0L; 0L; 0L; 158L; 48L; 0L; 0L; 0L; 0L; 0L; 0L; 86L; 0L; 0L; 0L; 2L; 0L; 0L; 0L; 94L; 64L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
      lm_std = [];
      lc_std = [];
    isok = true;
      v = 2L;
      fuel = 19L;
      result_expected = 110L;
    };  
  (*
    mov r0, r1
    mov r2, 30
    mov r3, 0L
    mov r4, 20
    mov r5, 0L
    lmul64 r3, r4
    lmul64 r5, r2
    add64 r5, r3
    mov64 r0, r2
    rsh64 r0, 0x20
    mov64 r3, r4
    rsh64 r3, 0x20
    mov64 r6, r3
    lmul64 r6, r0
    add64 r5, r6
    lsh64 r4, 0x20
    rsh64 r4, 0x20
    mov64 r6, r4
    lmul64 r6, r0
    lsh64 r2, 0x20
    rsh64 r2, 0x20
    lmul64 r4, r2
    mov64 r0, r4
    rsh64 r0, 0x20
    add64 r0, r6
    mov64 r6, r0
    rsh64 r6, 0x20
    add64 r5, r6
    lmul64 r3, r2
    lsh64 r0, 0x20
    rsh64 r0, 0x20
    add64 r0, r3
    mov64 r2, r0
    rsh64 r2, 0x20
    add64 r5, r2
    stxdw [r1+0x8], r5
    lsh64 r0, 0x20
    lsh64 r4, 0x20
    rsh64 r4, 0x20
    or64 r0, r4
    stxdw [r1+0x0], r0
    exit*)
  {
    dis = "test_lmul128";
    lp_std = [191L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 2L; 0L; 0L; 30L; 0L; 0L; 0L; 183L; 3L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 4L; 0L; 0L; 20L; 0L; 0L; 0L; 183L; 5L; 0L; 0L; 0L; 0L; 0L; 0L; 158L; 67L; 0L; 0L; 0L; 0L; 0L; 0L; 158L; 37L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 53L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 32L; 0L; 0L; 0L; 0L; 0L; 0L; 119L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 191L; 67L; 0L; 0L; 0L; 0L; 0L; 0L; 119L; 3L; 0L; 0L; 32L; 0L; 0L; 0L; 191L; 54L; 0L; 0L; 0L; 0L; 0L; 0L; 158L; 6L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 101L; 0L; 0L; 0L; 0L; 0L; 0L; 103L; 4L; 0L; 0L; 32L; 0L; 0L; 0L; 119L; 4L; 0L; 0L; 32L; 0L; 0L; 0L; 191L; 70L; 0L; 0L; 0L; 0L; 0L; 0L; 158L; 6L; 0L; 0L; 0L; 0L; 0L; 0L; 103L; 2L; 0L; 0L; 32L; 0L; 0L; 0L; 119L; 2L; 0L; 0L; 32L; 0L; 0L; 0L; 158L; 36L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 64L; 0L; 0L; 0L; 0L; 0L; 0L; 119L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 15L; 96L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 6L; 0L; 0L; 0L; 0L; 0L; 0L; 119L; 6L; 0L; 0L; 32L; 0L; 0L; 0L; 15L; 101L; 0L; 0L; 0L; 0L; 0L; 0L; 158L; 35L; 0L; 0L; 0L; 0L; 0L; 0L; 103L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 119L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 15L; 48L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 2L; 0L; 0L; 0L; 0L; 0L; 0L; 119L; 2L; 0L; 0L; 32L; 0L; 0L; 0L; 15L; 37L; 0L; 0L; 0L; 0L; 0L; 0L; 123L; 81L; 8L; 0L; 0L; 0L; 0L; 0L; 103L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 103L; 4L; 0L; 0L; 32L; 0L; 0L; 0L; 119L; 4L; 0L; 0L; 32L; 0L; 0L; 0L; 79L; 64L; 0L; 0L; 0L; 0L; 0L; 0L; 123L; 1L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L]; 
    lm_std = [0L; 16L];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 42L;
    result_expected = 600L;
  };
(*
    mov32 r0, 0L
    mov32 r1, 1
    mov32 r2, 2
    mov32 r3, 3
    mov32 r4, 4
    mov32 r5, 5
    mov32 r6, 6
    mov32 r7, 7
    mov32 r8, 8
    or32 r0, r5
    or32 r0, 0xa0
    and32 r0, 0xa3
    mov32 r9, 0x91
    and32 r0, r9
    lsh32 r0, 22
    lsh32 r0, r8
    rsh32 r0, 19
    rsh32 r0, r7
    xor32 r0, 0x03
    xor32 r0, r2
    exit*)
  {
    dis = "test_alu32_logic";
    lp_std = [180L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 180L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 180L; 2L; 0L; 0L; 2L; 0L; 0L; 0L; 180L; 3L; 0L; 0L; 3L; 0L; 0L; 0L; 180L; 4L; 0L; 0L; 4L; 0L; 0L; 0L; 180L; 5L; 0L; 0L; 5L; 0L; 0L; 0L; 180L; 6L; 0L; 0L; 6L; 0L; 0L; 0L; 180L; 7L; 0L; 0L; 7L; 0L; 0L; 0L; 180L; 8L; 0L; 0L; 8L; 0L; 0L; 0L; 76L; 80L; 0L; 0L; 0L; 0L; 0L; 0L; 68L; 0L; 0L; 0L; 160L; 0L; 0L; 0L; 84L; 0L; 0L; 0L; 163L; 0L; 0L; 0L; 180L; 9L; 0L; 0L; 145L; 0L; 0L; 0L; 92L; 144L; 0L; 0L; 0L; 0L; 0L; 0L; 100L; 0L; 0L; 0L; 22L; 0L; 0L; 0L; 108L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 116L; 0L; 0L; 0L; 19L; 0L; 0L; 0L; 124L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 164L; 0L; 0L; 0L; 3L; 0L; 0L; 0L; 172L; 32L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L]; 
    lm_std = [0L; 16L];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 21L;
    result_expected = 0x11L;
  };
(*
    mov r0, 0L
    mov r1, 1
    mov r2, 2
    mov r3, 3
    mov r4, 4
    mov r5, 5
    mov r6, 6
    mov r7, 7
    mov r8, 8
    or r0, r5
    or r0, 0xa0
    and r0, 0xa3
    mov r9, 0x91
    and r0, r9
    lsh r0, 32
    lsh r0, 22
    lsh r0, r8
    rsh r0, 32
    rsh r0, 19
    rsh r0, r7
    xor r0, 0x03
    xor r0, r2
    exit*)
  {
    dis = "test_alu64_logic";
    lp_std = [183L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 183L; 2L; 0L; 0L; 2L; 0L; 0L; 0L; 183L; 3L; 0L; 0L; 3L; 0L; 0L; 0L; 183L; 4L; 0L; 0L; 4L; 0L; 0L; 0L; 183L; 5L; 0L; 0L; 5L; 0L; 0L; 0L; 183L; 6L; 0L; 0L; 6L; 0L; 0L; 0L; 183L; 7L; 0L; 0L; 7L; 0L; 0L; 0L; 183L; 8L; 0L; 0L; 8L; 0L; 0L; 0L; 79L; 80L; 0L; 0L; 0L; 0L; 0L; 0L; 71L; 0L; 0L; 0L; 160L; 0L; 0L; 0L; 87L; 0L; 0L; 0L; 163L; 0L; 0L; 0L; 183L; 9L; 0L; 0L; 145L; 0L; 0L; 0L; 95L; 144L; 0L; 0L; 0L; 0L; 0L; 0L; 103L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 103L; 0L; 0L; 0L; 22L; 0L; 0L; 0L; 111L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 119L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 119L; 0L; 0L; 0L; 19L; 0L; 0L; 0L; 127L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 167L; 0L; 0L; 0L; 3L; 0L; 0L; 0L; 175L; 32L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L]; 
    lm_std = [0L; 16L];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 23L;
    result_expected = 0x11L;
  };
  (*
    mov r0, 8
    mov32 r1, 0x00000001
    hor64 r1, 0x00000001
    arsh32 r0, r1
    exit*)
  {
    dis = "test_arsh32_high_shift";
    lp_std = [183L; 0L; 0L; 0L; 8L; 0L; 0L; 0L; 180L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 247L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 204L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 5L;
    result_expected = 0x4L;   
  };
  (*
    mov32 r0, 0xf8
    lsh32 r0, 28
    arsh32 r0, 16
    exit*)
  {
    dis = "test_arsh32_imm";
    lp_std = [180L; 0L; 0L; 0L; 248L; 0L; 0L; 0L; 100L; 0L; 0L; 0L; 28L; 0L; 0L; 0L; 196L; 0L; 0L; 0L; 16L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 4L;
    result_expected = 0xffff8000L;   
  };
  (*
    mov32 r0, 0xf8
    mov32 r1, 16
    lsh32 r0, 28
    arsh32 r0, r1
    exit*)
  {
    dis = "test_arsh32_reg";
    lp_std = [180L; 0L; 0L; 0L; 248L; 0L; 0L; 0L; 180L; 1L; 0L; 0L; 16L; 0L; 0L; 0L; 100L; 0L; 0L; 0L; 28L; 0L; 0L; 0L; 204L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 5L;
    result_expected = 0xffff8000L;   
  };
  (*
    mov32 r0, 1
    lsh r0, 63
    arsh r0, 55
    mov32 r1, 5
    arsh r0, r1
    exit*)
  {
    dis = "test_arsh64";
    lp_std = [180L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 103L; 0L; 0L; 0L; 63L; 0L; 0L; 0L; 199L; 0L; 0L; 0L; 55L; 0L; 0L; 0L; 180L; 1L; 0L; 0L; 5L; 0L; 0L; 0L; 207L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 6L;
    result_expected = 0xfffffffffffffff8L;    
  };
  (*
    mov r0, 0x1
    mov r7, 4
    lsh r0, r7
    exit*)
  {
    dis = "test_lsh64_reg";
    lp_std = [183L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 183L; 7L; 0L; 0L; 4L; 0L; 0L; 0L; 111L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 64L;
    result_expected = 0x10L;   
  };
  (*
    xor r0, r0
    add r0, -1
    rsh32 r0, 8
    exit*)
  {
    dis = "test_rhs32_imm";
    lp_std = [175L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 7L; 0L; 0L; 0L; 255L; 255L; 255L; 255L; 116L; 0L; 0L; 0L; 8L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 4L;
    result_expected = 0x00ffffffL;   
  };
  (*
    mov r0, 0x10
    mov r7, 4
    rsh r0, r7
    exit*)
  {
    dis = "test_rsh64_reg";
    lp_std = [183L; 0L; 0L; 0L; 16L; 0L; 0L; 0L; 183L; 7L; 0L; 0L; 4L; 0L; 0L; 0L; 127L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 4L;
    result_expected = 0x1L;   
  };
  (*
    ldxh r0, [r1]
    be16 r0
    exit*)
  {
    dis = "test_be16";
    lp_std = [105L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 220L; 0L; 0L; 0L; 16L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x11L; 0x22L];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 3L;
    result_expected = 0x1122L;   
  };
  (*
    ldxdw r0, [r1]
    be16 r0
    exit*)
  {
    dis = "test_be16_high";
    lp_std = [121L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 220L; 0L; 0L; 0L; 16L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x11L; 0x22L; 0x33L; 0x44L; 0x55L; 0x66L; 0x77L; 0x88L];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 3L;
    result_expected = 0x1122L;   
  };
  (*
    ldxw r0, [r1]
    be32 r0
    exit*)
  {
    dis = "test_be32";
    lp_std = [97L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 220L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x11L; 0x22L; 0x33L; 0x44L];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 3L;
    result_expected = 0x11223344L;   
  };
  (*
    ldxdw r0, [r1]
    be32 r0
    exit*)
  {
    dis = "test_be32_high";
    lp_std = [121L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 220L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x11L; 0x22L; 0x33L; 0x44L; 0x55L; 0x66L; 0x77L; 0x88L];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 3L;
    result_expected = 0x11223344L;   
  };
  (*
    ldxdw r0, [r1]
    be64 r0
    exit*)
  {
    dis = "test_be64";
    lp_std = [121L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 220L; 0L; 0L; 0L; 64L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x11L; 0x22L; 0x33L; 0x44L; 0x55L; 0x66L; 0x77L; 0x88L];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 3L;
    result_expected = 0x1122334455667788L;   
  };
  (*
    hor64 r0, 0x10203040
    hor64 r0, 0x01020304
    exit*)
  {
    dis = "test_hor64";
    lp_std = [247L; 0L; 0L; 0L; 64L; 48L; 32L; 16L; 247L; 0L; 0L; 0L; 4L; 3L; 2L; 1L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 3L;
    result_expected = 0x1122334400000000L;   
  };
  (*
    ldxb r0, [r1+2]
    exit*)
  {
    dis = "test_ldxb";
    lp_std = [113L; 16L; 2L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0xaaL; 0xbbL; 0x11L; 0xccL; 0xddL];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 2L;
    result_expected = 0x11L;   
  };
  (*
    ldxh r0, [r1+2]
    exit*)
  {
    dis = "test_ldxh";
    lp_std = [105L; 16L; 2L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0xaaL; 0xbbL; 0x11L; 0x22L; 0xccL; 0xddL];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 2L;
    result_expected = 0x2211L;   
  };
  (*
    ldxw r0, [r1+2]
    exit*)
  {
    dis = "test_ldxw";
    lp_std = [97L; 16L; 2L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0xaaL; 0xbbL; 0x11L; 0x22L; 0x33L; 0x44L; 0xccL; 0xddL];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 2L;
    result_expected = 0x44332211L;   
  };
  (*
    mov r0, r1
    sth [r0], 0x1234
    ldxh r0, [r0]
    exit*)
  {
    dis = "test_ldxh_same_reg";
    lp_std = [191L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 106L; 0L; 0L; 0L; 52L; 18L; 0L; 0L; 105L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0xffL; 0xffL];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 4L;
    result_expected = 0x1234L;   
  };
  (* //Fatal error: exception Stack_overflow
    ldxdw r0, [r1+2]
    exit*)
  {
    dis = "test_lldxdw";
    lp_std = [121L; 16L; 2L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0xaaL; 0xbbL; 0x11L; 0x22L; 0x33L; 0x44L; 0x55L; 0x66L; 0x77L; 0x88L; 0xccL; 0xddL];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 2L;
    result_expected = 0x8877665544332211L;   
  };
  (*
    mov r0, r1
    ldxb r9, [r0+0]
    lsh r9, 0
    ldxb r8, [r0+1]
    lsh r8, 4
    ldxb r7, [r0+2]
    lsh r7, 8
    ldxb r6, [r0+3]
    lsh r6, 12
    ldxb r5, [r0+4]
    lsh r5, 16
    ldxb r4, [r0+5]
    lsh r4, 20
    ldxb r3, [r0+6]
    lsh r3, 24
    ldxb r2, [r0+7]
    lsh r2, 28
    ldxb r1, [r0+8]
    lsh r1, 32
    ldxb r0, [r0+9]
    lsh r0, 36
    or r0, r1
    or r0, r2
    or r0, r3
    or r0, r4
    or r0, r5
    or r0, r6
    or r0, r7
    or r0, r8
    or r0, r9
    exit*)
  {
    dis = "test_ldxb_all";
    lp_std = [191L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 113L; 9L; 0L; 0L; 0L; 0L; 0L; 0L; 103L; 9L; 0L; 0L; 0L; 0L; 0L; 0L; 113L; 8L; 1L; 0L; 0L; 0L; 0L; 0L; 103L; 8L; 0L; 0L; 4L; 0L; 0L; 0L; 113L; 7L; 2L; 0L; 0L; 0L; 0L; 0L; 103L; 7L; 0L; 0L; 8L; 0L; 0L; 0L; 113L; 6L; 3L; 0L; 0L; 0L; 0L; 0L; 103L; 6L; 0L; 0L; 12L; 0L; 0L; 0L; 113L; 5L; 4L; 0L; 0L; 0L; 0L; 0L; 103L; 5L; 0L; 0L; 16L; 0L; 0L; 0L; 113L; 4L; 5L; 0L; 0L; 0L; 0L; 0L; 103L; 4L; 0L; 0L; 20L; 0L; 0L; 0L; 113L; 3L; 6L; 0L; 0L; 0L; 0L; 0L; 103L; 3L; 0L; 0L; 24L; 0L; 0L; 0L; 113L; 2L; 7L; 0L; 0L; 0L; 0L; 0L; 103L; 2L; 0L; 0L; 28L; 0L; 0L; 0L; 113L; 1L; 8L; 0L; 0L; 0L; 0L; 0L; 103L; 1L; 0L; 0L; 32L; 0L; 0L; 0L; 113L; 0L; 9L; 0L; 0L; 0L; 0L; 0L; 103L; 0L; 0L; 0L; 36L; 0L; 0L; 0L; 79L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 32L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 48L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 64L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 80L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 96L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 144L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x00L; 0x01L; 0x02L; 0x03L; 0x04L; 0x05L; 0x06L; 0x07L; 0x08L; 0x09L];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 31L;
    result_expected = 0x9876543210L;   
  };
  (*
    mov r0, r1
    ldxh r9, [r0+0]
    be16 r9
    lsh r9, 0
    ldxh r8, [r0+2]
    be16 r8
    lsh r8, 4
    ldxh r7, [r0+4]
    be16 r7
    lsh r7, 8
    ldxh r6, [r0+6]
    be16 r6
    lsh r6, 12
    ldxh r5, [r0+8]
    be16 r5
    lsh r5, 16
    ldxh r4, [r0+10]
    be16 r4
    lsh r4, 20
    ldxh r3, [r0+12]
    be16 r3
    lsh r3, 24
    ldxh r2, [r0+14]
    be16 r2
    lsh r2, 28
    ldxh r1, [r0+16]
    be16 r1
    lsh r1, 32
    ldxh r0, [r0+18]
    be16 r0
    lsh r0, 36
    or r0, r1
    or r0, r2
    or r0, r3
    or r0, r4
    or r0, r5
    or r0, r6
    or r0, r7
    or r0, r8
    or r0, r9
    exit*)
  {
    dis = "test_ldxh_all";
    lp_std = [191L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 105L; 9L; 0L; 0L; 0L; 0L; 0L; 0L; 220L; 9L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 9L; 0L; 0L; 0L; 0L; 0L; 0L; 105L; 8L; 2L; 0L; 0L; 0L; 0L; 0L; 220L; 8L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 8L; 0L; 0L; 4L; 0L; 0L; 0L; 105L; 7L; 4L; 0L; 0L; 0L; 0L; 0L; 220L; 7L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 7L; 0L; 0L; 8L; 0L; 0L; 0L; 105L; 6L; 6L; 0L; 0L; 0L; 0L; 0L; 220L; 6L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 6L; 0L; 0L; 12L; 0L; 0L; 0L; 105L; 5L; 8L; 0L; 0L; 0L; 0L; 0L; 220L; 5L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 5L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 4L; 10L; 0L; 0L; 0L; 0L; 0L; 220L; 4L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 4L; 0L; 0L; 20L; 0L; 0L; 0L; 105L; 3L; 12L; 0L; 0L; 0L; 0L; 0L; 220L; 3L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 3L; 0L; 0L; 24L; 0L; 0L; 0L; 105L; 2L; 14L; 0L; 0L; 0L; 0L; 0L; 220L; 2L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 2L; 0L; 0L; 28L; 0L; 0L; 0L; 105L; 1L; 16L; 0L; 0L; 0L; 0L; 0L; 220L; 1L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 1L; 0L; 0L; 32L; 0L; 0L; 0L; 105L; 0L; 18L; 0L; 0L; 0L; 0L; 0L; 220L; 0L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 0L; 0L; 0L; 36L; 0L; 0L; 0L; 79L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 32L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 48L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 64L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 80L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 96L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 144L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x02L; 0x00L; 0x03L; 0x00L; 0x04L; 0x00L; 0x05L; 0x00L; 0x06L; 0x00L; 0x07L; 0x00L; 0x08L; 0x00L; 0x09L];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 41L;
    result_expected = 0x9876543210L;   
  };
  (*
    mov r0, r1
    ldxh r9, [r0+0]
    be16 r9
    ldxh r8, [r0+2]
    be16 r8
    ldxh r7, [r0+4]
    be16 r7
    ldxh r6, [r0+6]
    be16 r6
    ldxh r5, [r0+8]
    be16 r5
    ldxh r4, [r0+10]
    be16 r4
    ldxh r3, [r0+12]
    be16 r3
    ldxh r2, [r0+14]
    be16 r2
    ldxh r1, [r0+16]
    be16 r1
    ldxh r0, [r0+18]
    be16 r0
    or r0, r1
    or r0, r2
    or r0, r3
    or r0, r4
    or r0, r5
    or r0, r6
    or r0, r7
    or r0, r8
    or r0, r9
    exit*)
  {
    dis = "test_ldxh_all2";
    lp_std = [191L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 105L; 9L; 0L; 0L; 0L; 0L; 0L; 0L; 220L; 9L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 8L; 2L; 0L; 0L; 0L; 0L; 0L; 220L; 8L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 7L; 4L; 0L; 0L; 0L; 0L; 0L; 220L; 7L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 6L; 6L; 0L; 0L; 0L; 0L; 0L; 220L; 6L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 5L; 8L; 0L; 0L; 0L; 0L; 0L; 220L; 5L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 4L; 10L; 0L; 0L; 0L; 0L; 0L; 220L; 4L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 3L; 12L; 0L; 0L; 0L; 0L; 0L; 220L; 3L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 2L; 14L; 0L; 0L; 0L; 0L; 0L; 220L; 2L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 1L; 16L; 0L; 0L; 0L; 0L; 0L; 220L; 1L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 0L; 18L; 0L; 0L; 0L; 0L; 0L; 220L; 0L; 0L; 0L; 16L; 0L; 0L; 0L; 79L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 32L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 48L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 64L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 80L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 96L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 144L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x00L; 0x01L; 0x00L; 0x02L; 0x00L; 0x04L; 0x00L; 0x08L; 0x00L; 0x10L; 0x00L; 0x20L; 0x00L; 0x40L; 0x00L; 0x80L; 0x01L; 0x00L; 0x02L; 0x00L];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 31L;
    result_expected = 0x3ffL;   
  };
  (*
    mov r0, r1
    ldxw r9, [r0+0]
    be32 r9
    ldxw r8, [r0+4]
    be32 r8
    ldxw r7, [r0+8]
    be32 r7
    ldxw r6, [r0+12]
    be32 r6
    ldxw r5, [r0+16]
    be32 r5
    ldxw r4, [r0+20]
    be32 r4
    ldxw r3, [r0+24]
    be32 r3
    ldxw r2, [r0+28]
    be32 r2
    ldxw r1, [r0+32]
    be32 r1
    ldxw r0, [r0+36]
    be32 r0
    or r0, r1
    or r0, r2
    or r0, r3
    or r0, r4
    or r0, r5
    or r0, r6
    or r0, r7
    or r0, r8
    or r0, r9
    exit*)
  {
    dis = "test_ldxw_all";
    lp_std = [191L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 97L; 9L; 0L; 0L; 0L; 0L; 0L; 0L; 220L; 9L; 0L; 0L; 32L; 0L; 0L; 0L; 97L; 8L; 4L; 0L; 0L; 0L; 0L; 0L; 220L; 8L; 0L; 0L; 32L; 0L; 0L; 0L; 97L; 7L; 8L; 0L; 0L; 0L; 0L; 0L; 220L; 7L; 0L; 0L; 32L; 0L; 0L; 0L; 97L; 6L; 12L; 0L; 0L; 0L; 0L; 0L; 220L; 6L; 0L; 0L; 32L; 0L; 0L; 0L; 97L; 5L; 16L; 0L; 0L; 0L; 0L; 0L; 220L; 5L; 0L; 0L; 32L; 0L; 0L; 0L; 97L; 4L; 20L; 0L; 0L; 0L; 0L; 0L; 220L; 4L; 0L; 0L; 32L; 0L; 0L; 0L; 97L; 3L; 24L; 0L; 0L; 0L; 0L; 0L; 220L; 3L; 0L; 0L; 32L; 0L; 0L; 0L; 97L; 2L; 28L; 0L; 0L; 0L; 0L; 0L; 220L; 2L; 0L; 0L; 32L; 0L; 0L; 0L; 97L; 1L; 32L; 0L; 0L; 0L; 0L; 0L; 220L; 1L; 0L; 0L; 32L; 0L; 0L; 0L; 97L; 0L; 36L; 0L; 0L; 0L; 0L; 0L; 220L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 79L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 32L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 48L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 64L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 80L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 96L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 144L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std =[
      0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x02L;
      0x00L; 0x00L; 0x00L; 0x04L; 0x00L; 0x00L; 0x00L; 0x08L;
      0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L;
      0x00L; 0x00L; 0x04L; 0x00L; 0x00L; 0x00L; 0x08L; 0x00L;
      0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 31L;
    result_expected = 0x030f0fL;   
  };
(*
    stb [r1+2], 0x11
    ldxb r0, [r1+2]
    exit
*)
  {
    dis = "test_stb";
    lp_std = [114L; 1L; 2L; 0L; 17L; 0L; 0L; 0L; 113L; 16L; 2L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0xaaL; 0xbbL; 0xffL; 0xccL; 0xddL];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 3L;
    result_expected = 0x11L;
  };
(*
    sth [r1+2], 0x2211
    ldxh r0, [r1+2]
    exit
*)
  {
    dis = "test_sth";
    lp_std = [0x6aL; 0x01L; 0x02L; 0x00L; 0x11L; 0x22L; 0x00L; 0x00L; 0x69L; 0x10L; 0x02L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [0xaaL; 0xbbL; 0xffL; 0xffL; 0xccL; 0xddL];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 3L;
    result_expected = 0x2211L;
  };
(*
    stw [r1+2], 0x44332211
    ldxw r0, [r1+2]
    exit
*)
  {
    dis = "test_stw";
    lp_std = [0x62L; 0x01L; 0x02L; 0x00L; 0x11L; 0x22L; 0x33L; 0x44L; 0x61L; 0x10L; 0x02L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [0xaaL; 0xbbL; 0xffL; 0xffL; 0xffL; 0xffL; 0xccL; 0xddL];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 3L;
    result_expected = 0x44332211L;
  };
(*
    stdw [r1+2], 0x44332211
    ldxdw r0, [r1+2]
    exit
*)
{
  dis = "test_stdw";
  lp_std = [0x7aL; 0x01L; 0x02L; 0x00L; 0x11L; 0x22L; 0x33L; 0x44L; 0x79L; 0x10L; 0x02L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
  lm_std = [0xaaL; 0xbbL; 0xffL; 0xffL; 0xffL; 0xffL; 0xffL; 0xffL; 0xffL; 0xccL; 0xddL];
  lc_std = [];
    isok = true;
  v = 2L;
  fuel = 3L;
  result_expected = 0x44332211L;
};
(*
    mov32 r2, 0x11
    stxb [r1+2], r2
    ldxb r0, [r1+2]
    exit
*)
  {
    dis = "test_stxb";
    lp_std = [0xb4L; 0x02L; 0x00L; 0x00L; 0x11L; 0x00L; 0x00L; 0x00L; 0x73L; 0x21L; 0x02L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x71L; 0x10L; 0x02L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [0xaaL; 0xbbL; 0xffL; 0xccL; 0xddL];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 4L;
    result_expected = 0x11L;
  };
(*
    mov32 r2, 0x2211
    stxh [r1+2], r2
    ldxh r0, [r1+2]
    exit
*)
  {
    dis = "test_stxh";
    lp_std = [0xb4L; 0x02L; 0x00L; 0x00L; 0x11L; 0x22L; 0x00L; 0x00L; 0x6bL; 0x21L; 0x02L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x69L; 0x10L; 0x02L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [0xaaL; 0xbbL; 0xffL; 0xffL; 0xccL; 0xddL];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 4L;
    result_expected = 0x2211L;
  };
(*
    mov32 r2, 0x44332211
    stxw [r1+2], r2
    ldxw r0, [r1+2]
    exit
*)
  {
    dis = "test_stxw";
    lp_std = [0xb4L; 0x02L; 0x00L; 0x00L; 0x11L; 0x22L; 0x33L; 0x44L; 0x63L; 0x21L; 0x02L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x61L; 0x10L; 0x02L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [0xaaL; 0xbbL; 0xffL; 0xffL; 0xffL; 0xffL; 0xccL; 0xddL];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 4L;
    result_expected = 0x44332211L;
  };
(*
    mov r2, -2005440939
    lsh r2, 32
    or r2, 0x44332211
    stxdw [r1+2], r2
    ldxdw r0, [r1+2]
    exit
*)
  {
    dis = "test_stxdw";
    lp_std = [0xb7L; 0x02L; 0x00L; 0x00L; 0x55L; 0x66L; 0x77L; 0x88L; 0x67L; 0x02L; 0x00L; 0x00L; 0x20L; 0x00L; 0x00L; 0x00L; 0x47L; 0x02L; 0x00L; 0x00L; 0x11L; 0x22L; 0x33L; 0x44L; 0x7bL; 0x21L; 0x02L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x79L; 0x10L; 0x02L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [0xaaL; 0xbbL; 0xffL; 0xffL; 0xffL; 0xffL; 0xffL; 0xffL; 0xffL; 0xccL; 0xddL];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 6L;
    result_expected = 0x8877665544332211L;
  };
(*
    mov r0, 0xf0
    mov r2, 0xf2
    mov r3, 0xf3
    mov r4, 0xf4
    mov r5, 0xf5
    mov r6, 0xf6
    mov r7, 0xf7
    mov r8, 0xf8
    stxb [r1], r0
    stxb [r1+1], r2
    stxb [r1+2], r3
    stxb [r1+3], r4
    stxb [r1+4], r5
    stxb [r1+5], r6
    stxb [r1+6], r7
    stxb [r1+7], r8
    ldxdw r0, [r1]
    be64 r0
    exit
*)
  {
    dis = "test_stxb_all";
    lp_std = [0xb7L; 0x00L; 0x00L; 0x00L; 0xf0L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x02L; 0x00L; 0x00L; 0xf2L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x03L; 0x00L; 0x00L; 0xf3L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x04L; 0x00L; 0x00L; 0xf4L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x05L; 0x00L; 0x00L; 0xf5L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x06L; 0x00L; 0x00L; 0xf6L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x07L; 0x00L; 0x00L; 0xf7L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x08L; 0x00L; 0x00L; 0xf8L; 0x00L; 0x00L; 0x00L; 0x73L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x73L; 0x21L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x73L; 0x31L; 0x02L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x73L; 0x41L; 0x03L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x73L; 0x51L; 0x04L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x73L; 0x61L; 0x05L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x73L; 0x71L; 0x06L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x73L; 0x81L; 0x07L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x79L; 0x10L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xdcL; 0x00L; 0x00L; 0x00L; 0x40L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [0xffL; 0xffL; 0xffL; 0xffL; 0xffL; 0xffL; 0xffL; 0xffL];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 19L;
    result_expected = 0xf0f2f3f4f5f6f7f8L;
  };
(*
    mov r0, r1
    mov r1, 0xf1
    mov r9, 0xf9
    stxb [r0], r1
    stxb [r0+1], r9
    ldxh r0, [r0]
    be16 r0
    exit
*)
  {
    dis = "test_stxb_all2";
    lp_std = [0xbfL; 0x10L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x01L; 0x00L; 0x00L; 0xf1L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x09L; 0x00L; 0x00L; 0xf9L; 0x00L; 0x00L; 0x00L; 0x73L; 0x10L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x73L; 0x90L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x69L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xdcL; 0x00L; 0x00L; 0x00L; 0x10L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [0xffL; 0xffL];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 8L;
    result_expected = 0xf1f9L;
  };
(*
    mov r0, r1
    ldxb r9, [r0+0]
    stxb [r0+1], r9
    ldxb r8, [r0+1]
    stxb [r0+2], r8
    ldxb r7, [r0+2]
    stxb [r0+3], r7
    ldxb r6, [r0+3]
    stxb [r0+4], r6
    ldxb r5, [r0+4]
    stxb [r0+5], r5
    ldxb r4, [r0+5]
    stxb [r0+6], r4
    ldxb r3, [r0+6]
    stxb [r0+7], r3
    ldxb r2, [r0+7]
    stxb [r0+8], r2
    ldxb r1, [r0+8]
    stxb [r0+9], r1
    ldxb r0, [r0+9]
    exit
*)
  {
    dis = "test_stxb_chain";
    lp_std = [0xbfL; 0x10L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x71L; 0x09L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x73L; 0x90L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x71L; 0x08L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x73L; 0x80L; 0x02L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x71L; 0x07L; 0x02L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x73L; 0x70L; 0x03L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x71L; 0x06L; 0x03L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x73L; 0x60L; 0x04L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x71L; 0x05L; 0x04L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x73L; 0x50L; 0x05L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x71L; 0x04L; 0x05L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x73L; 0x40L; 0x06L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x71L; 0x03L; 0x06L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x73L; 0x30L; 0x07L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x71L; 0x02L; 0x07L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x73L; 0x20L; 0x08L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x71L; 0x01L; 0x08L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x73L; 0x10L; 0x09L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x71L; 0x00L; 0x09L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [0x2aL; 0x0L; 0x0L; 0x0L; 0x0L; 0x0L; 0x0L; 0x0L; 0x0L];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 21L;
    result_expected = 0x2aL;
  };
(*
exit
*)
  {
    dis = "test_exit_without_value";
    lp_std = [0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 1L;
    result_expected = 0x0L;
  };
(*
    mov r0, 0
    exit
*)
  {
      dis = "test_exit";
      lp_std = [0xb7L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
      lm_std = [];
      lc_std = [];
    isok = true;
      v = 2L;
      fuel = 2L;
      result_expected = 0x0L;
  };
(*
    mov r0, 3
    exit
    mov r0, 4
    exit
*)
  {
    dis = "test_early_exit";
    lp_std = [0xb7L; 0x00L; 0x00L; 0x00L; 0x03L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x00L; 0x00L; 0x00L; 0x04L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 2L;
    result_expected = 0x3L;
  };
(*
    mov r0, 1
    ja +1
    mov r0, 2
    exit
*)
  {
    dis = "test_ja";
    lp_std = [0xb7L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x05L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 3L;
    result_expected = 0x1L;
  };
(*
  mov32 r0, 0
    mov32 r1, 0xa
    jeq r1, 0xb, +4
    mov32 r0, 1
    mov32 r1, 0xb
    jeq r1, 0xb, +1
    mov32 r0, 2
    exit
*)
  {
    dis = "test_jeq_imm";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x0aL; 0x00L; 0x00L; 0x00L; 0x15L; 0x01L; 0x04L; 0x00L; 0x0bL; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x0bL; 0x00L; 0x00L; 0x00L; 0x15L; 0x01L; 0x01L; 0x00L; 0x0bL; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 7L;
    result_expected = 0x1L;
  };

(*
    mov32 r0, 0
    mov32 r1, 0xa
    mov32 r2, 0xb
    jeq r1, r2, +4
    mov32 r0, 1
    mov32 r1, 0xb
    jeq r1, r2, +1
    mov32 r0, 2
    exit
*)
  {
    dis = "test_jeq_reg";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x0aL; 0x00L; 0x00L; 0x00L; 0xb4L; 0x02L; 0x00L; 0x00L; 0x0bL; 0x00L; 0x00L; 0x00L; 0x1dL; 0x21L; 0x04L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x0bL; 0x00L; 0x00L; 0x00L; 0x1dL; 0x21L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 8L;
    result_expected = 0x1L;
  };
(*
    mov32 r0, 0
    mov32 r1, 0xa
    jge r1, 0xb, +4
    mov32 r0, 1
    mov32 r1, 0xc
    jge r1, 0xb, +1
    mov32 r0, 2
    exit
*)
  {
    dis = "test_jge_imm";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x0aL; 0x00L; 0x00L; 0x00L; 0x35L; 0x01L; 0x04L; 0x00L; 0x0bL; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x0cL; 0x00L; 0x00L; 0x00L; 0x35L; 0x01L; 0x01L; 0x00L; 0x0bL; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 7L;
    result_expected = 0x1L;
  };

  (*
    mov32 r0, 0
    mov32 r1, 0xa
    mov32 r2, 0xb
    jge r1, r2, +4
    mov32 r0, 1
    mov32 r1, 0xb
    jge r1, r2, +1
    mov32 r0, 2
    exit
*)
  {
    dis = "test_jge_reg";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x0aL; 0x00L; 0x00L; 0x00L; 0xb4L; 0x02L; 0x00L; 0x00L; 0x0bL; 0x00L; 0x00L; 0x00L; 0x3dL; 0x21L; 0x04L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x0bL; 0x00L; 0x00L; 0x00L; 0x3dL; 0x21L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 8L;
    result_expected = 0x1L;
  };
(*
    mov32 r0, 0
    mov32 r1, 5
    jle r1, 4, +1
    jle r1, 6, +1
    exit
    jle r1, 5, +1
    exit
    mov32 r0, 1
    exit
*)
  {
    dis = "test_jle_imm";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x05L; 0x00L; 0x00L; 0x00L; 0xb5L; 0x01L; 0x01L; 0x00L; 0x04L; 0x00L; 0x00L; 0x00L; 0xb5L; 0x01L; 0x01L; 0x00L; 0x06L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb5L; 0x01L; 0x01L; 0x00L; 0x05L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 7L;
    result_expected = 0x1L;
  };
(*
    mov r0, 0
    mov r1, 5
    mov r2, 4
    mov r3, 6
    jle r1, r2, +2
    jle r1, r1, +1
    exit
    jle r1, r3, +1
    exit
    mov r0, 1
    exit
*)
  {
    dis = "test_jle_reg";
    lp_std = [0xb7L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x01L; 0x00L; 0x00L; 0x05L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x02L; 0x00L; 0x00L; 0x04L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x03L; 0x00L; 0x00L; 0x06L; 0x00L; 0x00L; 0x00L; 0xbdL; 0x21L; 0x02L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xbdL; 0x11L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xbdL; 0x31L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 9L;
    result_expected = 0x1L;
  };
(*
    mov32 r0, 0
    mov32 r1, 5
    jgt r1, 6, +2
    jgt r1, 5, +1
    jgt r1, 4, +1
    exit
    mov32 r0, 1
    exit
*)
  {
    dis = "test_jgt_imm";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x05L; 0x00L; 0x00L; 0x00L; 0x25L; 0x01L; 0x02L; 0x00L; 0x06L; 0x00L; 0x00L; 0x00L; 0x25L; 0x01L; 0x01L; 0x00L; 0x05L; 0x00L; 0x00L; 0x00L; 0x25L; 0x01L; 0x01L; 0x00L; 0x04L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 7L;
    result_expected = 0x1L;
  };
(*
    mov r0, 0
    mov r1, 5
    mov r2, 6
    mov r3, 4
    jgt r1, r2, +2
    jgt r1, r1, +1
    jgt r1, r3, +1
    exit
    mov r0, 1
    exit
*)
  {
    dis = "test_jgt_reg";
    lp_std = [0xb7L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x01L; 0x00L; 0x00L; 0x05L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x02L; 0x00L; 0x00L; 0x06L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x03L; 0x00L; 0x00L; 0x04L; 0x00L; 0x00L; 0x00L; 0x2dL; 0x21L; 0x02L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x2dL; 0x11L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x2dL; 0x31L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 9L;
    result_expected = 0x1L;
  };
(*
    mov32 r0, 0
    mov32 r1, 5
    jlt r1, 4, +2
    jlt r1, 5, +1
    jlt r1, 6, +1
    exit
    mov32 r0, 1
    exit
*)
  {
    dis = "test_jlt_imm";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x05L; 0x00L; 0x00L; 0x00L; 0xa5L; 0x01L; 0x02L; 0x00L; 0x04L; 0x00L; 0x00L; 0x00L; 0xa5L; 0x01L; 0x01L; 0x00L; 0x05L; 0x00L; 0x00L; 0x00L; 0xa5L; 0x01L; 0x01L; 0x00L; 0x06L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 7L;
    result_expected = 0x1L;
  };
(*
    mov r0, 0
    mov r1, 5
    mov r2, 4
    mov r3, 6
    jlt r1, r2, +2
    jlt r1, r1, +1
    jlt r1, r3, +1
    exit
    mov r0, 1
    exit
*)
  {
    dis = "test_jlt_reg";
    lp_std = [0xb7L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x01L; 0x00L; 0x00L; 0x05L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x02L; 0x00L; 0x00L; 0x04L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x03L; 0x00L; 0x00L; 0x06L; 0x00L; 0x00L; 0x00L; 0xadL; 0x21L; 0x02L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xadL; 0x11L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xadL; 0x31L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 9L;
    result_expected = 0x1L;
  };
(*
    mov32 r0, 0
    mov32 r1, 0xb
    jne r1, 0xb, +4
    mov32 r0, 1
    mov32 r1, 0xa
    jne r1, 0xb, +1
    mov32 r0, 2
    exit
*)
  {
    dis = "test_jne_imm";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x0bL; 0x00L; 0x00L; 0x00L; 0x55L; 0x01L; 0x04L; 0x00L; 0x0bL; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x0aL; 0x00L; 0x00L; 0x00L; 0x55L; 0x01L; 0x01L; 0x00L; 0x0bL; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 7L;
    result_expected = 0x1L;
  };
(*
    mov32 r0, 0
    mov32 r1, 0xb
    mov32 r2, 0xb
    jne r1, r2, +4
    mov32 r0, 1
    mov32 r1, 0xa
    jne r1, r2, +1
    mov32 r0, 2
    exit
*)
  {
    dis = "test_jne_reg";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x0bL; 0x00L; 0x00L; 0x00L; 0xb4L; 0x02L; 0x00L; 0x00L; 0x0bL; 0x00L; 0x00L; 0x00L; 0x5dL; 0x21L; 0x04L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x0aL; 0x00L; 0x00L; 0x00L; 0x5dL; 0x21L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 8L;
    result_expected = 0x1L;
  };
(*
    mov32 r0, 0
    mov32 r1, 0x7
    jset r1, 0x8, +4
    mov32 r0, 1
    mov32 r1, 0x9
    jset r1, 0x8, +1
    mov32 r0, 2
    exit
*)
  {
    dis = "test_jset_imm";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x07L; 0x00L; 0x00L; 0x00L; 0x45L; 0x01L; 0x04L; 0x00L; 0x08L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x09L; 0x00L; 0x00L; 0x00L; 0x45L; 0x01L; 0x01L; 0x00L; 0x08L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 7L;
    result_expected = 0x1L;
  };
(*
    mov32 r0, 0
    mov32 r1, 0x7
    mov32 r2, 0x8
    jset r1, r2, +4
    mov32 r0, 1
    mov32 r1, 0x9
    jset r1, r2, +1
    mov32 r0, 2
    exit
*)
  {
    dis = "test_jset_reg";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x07L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x02L; 0x00L; 0x00L; 0x08L; 0x00L; 0x00L; 0x00L; 0x4dL; 0x21L; 0x04L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x09L; 0x00L; 0x00L; 0x00L; 0x4dL; 0x21L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 8L;
    result_expected = 0x1L;
  };
(*
    mov32 r0, 0
    mov r1, -2
    jsge r1, -1, +5
    jsge r1, 0, +4
    mov32 r0, 1
    mov r1, -1
    jsge r1, -1, +1
    mov32 r0, 2
    exit
*)
  {
    dis = "test_jsge_imm";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x01L; 0x00L; 0x00L; 0xfeL; 0xffL; 0xffL; 0xffL; 0x75L; 0x01L; 0x05L; 0x00L; 0xffL; 0xffL; 0xffL; 0xffL; 0x75L; 0x01L; 0x04L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x01L; 0x00L; 0x00L; 0xffL; 0xffL; 0xffL; 0xffL; 0x75L; 0x01L; 0x01L; 0x00L; 0xffL; 0xffL; 0xffL; 0xffL; 0xb4L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 8L;
    result_expected = 0x1L;
  };
(*
    mov32 r0, 0
    mov r1, -2
    mov r2, -1
    mov32 r3, 0
    jsge r1, r2, +5
    jsge r1, r3, +4
    mov32 r0, 1
    mov r1, r2
    jsge r1, r2, +1
    mov32 r0, 2
    exit
*)
  {
    dis = "test_jsge_reg";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x01L; 0x00L; 0x00L; 0xfeL; 0xffL; 0xffL; 0xffL; 0xb7L; 0x02L; 0x00L; 0x00L; 0xffL; 0xffL; 0xffL; 0xffL; 0xb4L; 0x03L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x7dL; 0x21L; 0x05L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x7dL; 0x31L; 0x04L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0xbfL; 0x21L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x7dL; 0x21L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 10L;
    result_expected = 0x1L;
  };
(*
    mov32 r0, 0
    mov r1, -2
    jsle r1, -3, +1
    jsle r1, -1, +1
    exit
    mov32 r0, 1
    jsle r1, -2, +1
    mov32 r0, 2
    exit
*)
  {
    dis = "test_jsle_imm";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x01L; 0x00L; 0x00L; 0xfeL; 0xffL; 0xffL; 0xffL; 0xd5L; 0x01L; 0x01L; 0x00L; 0xfdL; 0xffL; 0xffL; 0xffL; 0xd5L; 0x01L; 0x01L; 0x00L; 0xffL; 0xffL; 0xffL; 0xffL; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0xd5L; 0x01L; 0x01L; 0x00L; 0xfeL; 0xffL; 0xffL; 0xffL; 0xb4L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 7L;
    result_expected = 0x1L;
  };
(*
    mov32 r0, 0
    mov r1, -1
    mov r2, -2
    mov32 r3, 0
    jsle r1, r2, +1
    jsle r1, r3, +1
    exit
    mov32 r0, 1
    mov r1, r2
    jsle r1, r2, +1
    mov32 r0, 2
    exit
*)
  {
    dis = "test_jsle_reg";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x01L; 0x00L; 0x00L; 0xffL; 0xffL; 0xffL; 0xffL; 0xb7L; 0x02L; 0x00L; 0x00L; 0xfeL; 0xffL; 0xffL; 0xffL; 0xb4L; 0x03L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xddL; 0x21L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xddL; 0x31L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0xbfL; 0x21L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xddL; 0x21L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 10L;
    result_expected = 0x1L;
  };
(*
    mov32 r0, 0
    mov r1, -2
    jsgt r1, -1, +4
    mov32 r0, 1
    mov32 r1, 0
    jsgt r1, -1, +1
    mov32 r0, 2
    exit
*)
  {
    dis = "test_jsgt_imm";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x01L; 0x00L; 0x00L; 0xfeL; 0xffL; 0xffL; 0xffL; 0x65L; 0x01L; 0x04L; 0x00L; 0xffL; 0xffL; 0xffL; 0xffL; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x65L; 0x01L; 0x01L; 0x00L; 0xffL; 0xffL; 0xffL; 0xffL; 0xb4L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 7L;
    result_expected = 0x1L;
  };
(*
    mov32 r0, 0
    mov r1, -2
    mov r2, -1
    jsgt r1, r2, +4
    mov32 r0, 1
    mov32 r1, 0
    jsgt r1, r2, +1
    mov32 r0, 2
    exit
*)
  {
    dis = "test_jsgt_reg";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x01L; 0x00L; 0x00L; 0xfeL; 0xffL; 0xffL; 0xffL; 0xb7L; 0x02L; 0x00L; 0x00L; 0xffL; 0xffL; 0xffL; 0xffL; 0x6dL; 0x21L; 0x04L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x6dL; 0x21L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 8L;
    result_expected = 0x1L;
  };
(*
    mov32 r0, 0
    mov r1, -2
    jslt r1, -3, +2
    jslt r1, -2, +1
    jslt r1, -1, +1
    exit
    mov32 r0, 1
    exit
*)
  {
    dis = "test_jslt_imm";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x01L; 0x00L; 0x00L; 0xfeL; 0xffL; 0xffL; 0xffL; 0xc5L; 0x01L; 0x02L; 0x00L; 0xfdL; 0xffL; 0xffL; 0xffL; 0xc5L; 0x01L; 0x01L; 0x00L; 0xfeL; 0xffL; 0xffL; 0xffL; 0xc5L; 0x01L; 0x01L; 0x00L; 0xffL; 0xffL; 0xffL; 0xffL; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 7L;
    result_expected = 0x1L;
  };
(*
    mov32 r0, 0
    mov r1, -2
    mov r2, -3
    mov r3, -1
    jslt r1, r1, +2
    jslt r1, r2, +1
    jslt r1, r3, +1
    exit
    mov32 r0, 1
    exit
*)
  {
    dis = "test_jslt_reg";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x01L; 0x00L; 0x00L; 0xfeL; 0xffL; 0xffL; 0xffL; 0xb7L; 0x02L; 0x00L; 0x00L; 0xfdL; 0xffL; 0xffL; 0xffL; 0xb7L; 0x03L; 0x00L; 0x00L; 0xffL; 0xffL; 0xffL; 0xffL; 0xcdL; 0x11L; 0x02L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xcdL; 0x21L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xcdL; 0x31L; 0x01L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb4L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 9L;
    result_expected = 0x1L;
  };
(*
    mov r1, 51
    stdw [r10-16], 0xab
    stdw [r10-8], 0xcd
    and r1, 1
    lsh r1, 3
    mov r2, r10
    add r2, r1
    ldxdw r0, [r2-16]
    exit
*)
  {
    dis = "test_stack1";
    lp_std = [0xb7L; 0x01L; 0x00L; 0x00L; 0x33L; 0x00L; 0x00L; 0x00L; 0x7aL; 0x0aL; 0xf0L; 0xffL; 0xabL; 0x00L; 0x00L; 0x00L; 0x7aL; 0x0aL; 0xf8L; 0xffL; 0xcdL; 0x00L; 0x00L; 0x00L; 0x57L; 0x01L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x67L; 0x01L; 0x00L; 0x00L; 0x03L; 0x00L; 0x00L; 0x00L; 0xbfL; 0xa2L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x0fL; 0x12L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x79L; 0x20L; 0xf0L; 0xffL; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 9L;
    result_expected = 0xcdL;
  };
(*
    mov r0, 0x7
    add r1, 0xa
    lsh r1, 0x20
    rsh r1, 0x20
    jeq r1, 0x0, +4
    mov r0, 0x7
    lmul r0, 0x7
    add r1, -1
    jne r1, 0x0, -3
    exit
*)
  {
    dis = "test_lmul_loop";
    lp_std = [0xb7L; 0x00L; 0x00L; 0x00L; 0x07L; 0x00L; 0x00L; 0x00L; 0x07L; 0x01L; 0x00L; 0x00L; 0x0aL; 0x00L; 0x00L; 0x00L; 0x67L; 0x01L; 0x00L; 0x00L; 0x20L; 0x00L; 0x00L; 0x00L; 0x77L; 0x01L; 0x00L; 0x00L; 0x20L; 0x00L; 0x00L; 0x00L; 0x15L; 0x01L; 0x04L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x00L; 0x00L; 0x00L; 0x07L; 0x00L; 0x00L; 0x00L; 0x96L; 0x00L; 0x00L; 0x00L; 0x07L; 0x00L; 0x00L; 0x00L; 0x07L; 0x01L; 0x00L; 0x00L; 0xffL; 0xffL; 0xffL; 0xffL; 0x55L; 0x01L; 0xfdL; 0xffL; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 37L;
    result_expected = 0x75db9c97L;
  };
(*
    mov r1, 67
    mov r0, 0x1
    mov r2, 0x2
    jgt r1, 0x2, +4
    ja +10
    add r2, 0x1
    mov r0, 0x1
    jge r2, r1, +7
    mov r3, r1
    udiv r3, r2
    lmul r3, r2
    mov r4, r1
    sub r4, r3
    mov r0, 0x0
    jne r4, 0x0, -10
    exit
*)
  {
    dis = "test_prime";
    lp_std = [0xb7L; 0x01L; 0x00L; 0x00L; 0x43L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x02L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x25L; 0x01L; 0x04L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x05L; 0x00L; 0x0aL; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x07L; 0x02L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x3dL; 0x12L; 0x07L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xbfL; 0x13L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x5eL; 0x23L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x9eL; 0x23L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xbfL; 0x14L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x1fL; 0x34L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x55L; 0x04L; 0xf6L; 0xffL; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 655L;
    result_expected = 0x1L;
  };
(*
    mov r2, 0xe
    ldxh r3, [r1+12]
    jne r3, 0x81, +2
    mov r2, 0x12
    ldxh r3, [r1+16]
    and r3, 0xffff
    jne r3, 0x8, +5
    add r1, r2
    mov r0, 0x1
    ldxw r1, [r1+16]
    and r1, 0xffffff
    jeq r1, 0x1a8c0, +1
    mov r0, 0x0
    exit
*)
  {
    dis = "test_subnet";
    lp_std = [0xb7L; 0x02L; 0x00L; 0x00L; 0x0eL; 0x00L; 0x00L; 0x00L; 0x69L; 0x13L; 0x0cL; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x55L; 0x03L; 0x02L; 0x00L; 0x81L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x02L; 0x00L; 0x00L; 0x12L; 0x00L; 0x00L; 0x00L; 0x69L; 0x13L; 0x10L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x57L; 0x03L; 0x00L; 0x00L; 0xffL; 0xffL; 0x00L; 0x00L; 0x55L; 0x03L; 0x05L; 0x00L; 0x08L; 0x00L; 0x00L; 0x00L; 0x0fL; 0x21L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x61L; 0x11L; 0x10L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x57L; 0x01L; 0x00L; 0x00L; 0xffL; 0xffL; 0xffL; 0x00L; 0x15L; 0x01L; 0x01L; 0x00L; 0xc0L; 0xa8L; 0x01L; 0x00L; 0xb7L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [0x0L; 0x0L; 0xc0L; 0x9fL; 0xa0L; 0x97L; 0x0L; 0xa0L; 0xccL; 0x3bL; 0xbfL; 0xfaL; 0x8L; 0x0L; 0x45L; 0x10L; 0x0L; 0x3cL; 0x46L; 0x3cL; 0x40L; 0x0L; 0x40L; 0x6L; 0x73L; 0x1cL; 0xc0L; 0xa8L; 0x1L; 0x2L; 0xc0L; 0xa8L; 0x1L; 0x1L; 0x6L; 0xeL; 0x0L; 0x17L; 0x99L; 0xc5L; 0xa0L; 0xecL; 0x0L; 0x0L; 0x0L; 0x0L; 0xa0L; 0x2L; 0x7dL; 0x78L; 0xe0L; 0xa3L; 0x0L; 0x0L; 0x2L; 0x4L; 0x5L; 0xb4L; 0x4L; 0x2L; 0x8L; 0xaL; 0x0L; 0x9cL; 0x27L; 0x24L; 0x0L; 0x0L; 0x0L; 0x0L; 0x1L; 0x3L; 0x3L; 0x0L];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 11L;
    result_expected = 0x1L;
  };
(*  
    lddw r0, 0x1122334455667788
    exit
*)
  {
    dis = "test_lddw1";
    lp_std = [24L; 0L; 0L; 0L; 136L; 119L; 102L; 85L; 0L; 0L; 0L; 0L; 68L; 51L; 34L; 17L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 2L;
    result_expected = 0x1122334455667788L;
  };
(*  
    lddw r0, 0x0000000080000000
    exit
*)
  {
    dis = "test_lddw2";
    lp_std = [24L; 0L; 0L; 0L; 0L; 0L; 0L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 2L;
    result_expected = 0x80000000L;
  };
(*
    mov r0, 0
    mov r1, 0
    mov r2, 0
    lddw r0, 0x1
    ja +2
    lddw r1, 0x1
    lddw r2, 0x1
    add r1, r2
    add r0, r1
    exit
*)
  {
    dis = "test_lddw3";
    lp_std = [183L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 1L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 2L; 0L; 0L; 0L; 0L; 0L; 0L; 24L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 5L; 0L; 2L; 0L; 0L; 0L; 0L; 0L; 24L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 24L; 2L; 0L; 0L; 1L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 33L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 9L;
    result_expected = 0x2L;
  };
(*  
    ldxh r0, [r1]
    le16 r0
    exit
*)
  {
    dis = "test_le16_1";
    lp_std = [105L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 212L; 0L; 0L; 0L; 16L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x22L; 0x11L];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 3L;
    result_expected = 0x1122L;
  };
(*  
    ldxdw r0, [r1]
    le16 r0
    exit
*)
  {
    dis = "test_le16_2";
    lp_std = [121L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 212L; 0L; 0L; 0L; 16L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x11L; 0x22L; 0x33L; 0x44L; 0x55L; 0x66L; 0x77L; 0x88L];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 3L;
    result_expected = 0x2211L;
  }; 
(*
    ldxw r0, [r1]
    le32 r0
    exit
*)
  {
    dis = "test_le_1";
    lp_std = [0x61L; 0x10L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xd4L; 0x00L; 0x00L; 0x00L; 0x20L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [0x44L; 0x33L; 0x22L; 0x11L];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 3L;
    result_expected = 0x11223344L;
  };
(*
    ldxdw r0, [r1]
    le32 r0
    exit
*)
  {
    dis = "test_le_2";
    lp_std = [0x79L; 0x10L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xd4L; 0x00L; 0x00L; 0x00L; 0x20L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [0x11L; 0x22L; 0x33L; 0x44L; 0x55L; 0x66L; 0x77L; 0x88L];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 3L;
    result_expected = 0x44332211L;
  };
(*
    ldxdw r0, [r1]
    le64 r0
    exit
*)
  {
    dis = "test_le64";
    lp_std = [0x79L; 0x10L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xd4L; 0x00L; 0x00L; 0x00L; 0x40L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [0x88L; 0x77L; 0x66L; 0x55L; 0x44L; 0x33L; 0x22L; 0x11L];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 3L;
    result_expected = 0x1122334455667788L;
  };
(*
    mov32 r0, 2
    neg32 r0
    exit
*)
  {
    dis = "test_neg_1";
    lp_std = [0xb4L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x84L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 3L;
    result_expected = 0xfffffffeL;
  };
(*
    mov r0, 2
    neg r0
    exit
*)
  {
    dis = "test_neg_2";
    lp_std = [0xb7L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L; 0x00L; 0x87L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 3L;
    result_expected = 0xfffffffffffffffeL;
  };
(*
    mov32 r0, 3
    sub32 r0, 1
    exit
*)
  {
    dis = "test_neg_3";
    lp_std = [180L; 0L; 0L; 0L; 3L; 0L; 0L; 0L; 20L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 3L;
    result_expected = 0x2L;
  };
(*
    mov r0, 3
    sub r0, 1
    exit
*)
  {
    dis = "test_neg_4";
    lp_std = [183L; 0L; 0L; 0L; 3L; 0L; 0L; 0L; 23L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 3L;
    result_expected = 0x2L;
  };
(*  
    mov r0, 3
    mul32 r0, 4
    exit
*)
{
  dis = "test_mul_1";
  lp_std = [183L; 0L; 0L; 0L; 3L; 0L; 0L; 0L; 36L; 0L; 0L; 0L; 4L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
  lm_std = [];
  lc_std = [];
    isok = true;
  v = 1L;
  fuel = 3L;
  result_expected = 0xcL;
}; 
(*  
    mov r0, 3
    mov r1, 4
    mul32 r0, r1
    exit
*)
  {
    dis = "test_mul_2";
    lp_std = [183L; 0L; 0L; 0L; 3L; 0L; 0L; 0L; 183L; 1L; 0L; 0L; 4L; 0L; 0L; 0L; 44L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 4L;
    result_expected = 0xcL;
  }; 
(*  
    mov r0, 0x40000001
    mov r1, 4
    mul32 r0, r1
    exit
*)
  {
    dis = "test_mul_3";
    lp_std = [183L; 0L; 0L; 0L; 1L; 0L; 0L; 64L; 183L; 1L; 0L; 0L; 4L; 0L; 0L; 0L; 44L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 4L;
    result_expected = 0x4L;
  };
(*  
      mov r0, 0x40000001
      mul r0, 4
      exit
*)
  {
    dis = "test_mul_4";
    lp_std = [183L; 0L; 0L; 0L; 1L; 0L; 0L; 64L; 39L; 0L; 0L; 0L; 4L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 3L;
    result_expected = 0x100000004L;
  };  
(*  
    mov r0, 0x40000001
    mov r1, 4
    mul r0, r1
    exit
*)
  {
    dis = "test_mul_5";
    lp_std = [183L; 0L; 0L; 0L; 1L; 0L; 0L; 64L; 183L; 1L; 0L; 0L; 4L; 0L; 0L; 0L; 47L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 4L;
    result_expected = 0x100000004L;
  }; 
(*  
    mov r0, -1
    mul32 r0, 4
    exit
*)
  {
    dis = "test_mul_6";
    lp_std = [183L; 0L; 0L; 0L; 255L; 255L; 255L; 255L; 36L; 0L; 0L; 0L; 4L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 3L;
    result_expected = 0xFFFFFFFFFFFFFFFCL;
  };  
(*  
    mov r0, 12
    lddw r1, 0x100000004
    div32 r0, r1
    exit
*)
  {
    dis = "test_div_1";
    lp_std = [183L; 0L; 0L; 0L; 12L; 0L; 0L; 0L; 24L; 1L; 0L; 0L; 4L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 60L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 4L;
    result_expected = 0x3L;
  }; 
(*  
    lddw r0, 0x10000000c
    div32 r0, 4
    exit
*)
  {
    dis = "test_div_2";
    lp_std = [24L; 0L; 0L; 0L; 12L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 52L; 0L; 0L; 0L; 4L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 3L;
    result_expected = 0x3L;
  }; 
(*  
    lddw r0, 0x10000000c
    mov r1, 4
    div32 r0, r1
    exit
*)
  {
    dis = "test_div_3";
    lp_std = [24L; 0L; 0L; 0L; 12L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 183L; 1L; 0L; 0L; 4L; 0L; 0L; 0L; 60L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 4L;
    result_expected = 0x3L;
  }; 
(*  
    mov r0, 0xc
    lsh r0, 32
    div r0, 4
    exit
*)
  {
    dis = "test_div_4";
    lp_std = [183L; 0L; 0L; 0L; 12L; 0L; 0L; 0L; 103L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 55L; 0L; 0L; 0L; 4L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 4L;
    result_expected = 0x300000000L;
  }; 
(*  
    mov r0, 0xc
    lsh r0, 32
    mov r1, 4
    div r0, r1
    exit
*)
  {
    dis = "test_div_5";
    lp_std = [183L; 0L; 0L; 0L; 12L; 0L; 0L; 0L; 103L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 183L; 1L; 0L; 0L; 4L; 0L; 0L; 0L; 63L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 5L;
    result_expected = 0x300000000L;
  }; 
(*  
    mov32 r0, 5748
    mod32 r0, 92
    mov32 r1, 13
    mod32 r0, r1
    exit
*)
  {
    dis = "test_mod_1";
    lp_std = [180L; 0L; 0L; 0L; 116L; 22L; 0L; 0L; 148L; 0L; 0L; 0L; 92L; 0L; 0L; 0L; 180L; 1L; 0L; 0L; 13L; 0L; 0L; 0L; 156L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 5L;
    result_expected = 0x5L;
  }; 
(*  
    lddw r0, 0x100000003
    mod32 r0, 3
    exit
*)
  {
    dis = "test_mod_2";
    lp_std = [24L; 0L; 0L; 0L; 3L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 148L; 0L; 0L; 0L; 3L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 3L;
    result_expected = 0x0L;
  }; 
 (*  
    mov32 r0, -1316649930
    lsh r0, 32
    or r0, 0x100dc5c8
    mov32 r1, 0xdde263e
    lsh r1, 32
    or r1, 0x3cbef7f3
    mod r0, r1
    mod r0, 0x658f1778
    exit
*)
  {
    dis = "test_mod_3";
    lp_std = [180L; 0L; 0L; 0L; 54L; 132L; 133L; 177L; 103L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 71L; 0L; 0L; 0L; 200L; 197L; 13L; 16L; 180L; 1L; 0L; 0L; 62L; 38L; 222L; 13L; 103L; 1L; 0L; 0L; 32L; 0L; 0L; 0L; 71L; 1L; 0L; 0L; 243L; 247L; 190L; 60L; 159L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 151L; 0L; 0L; 0L; 120L; 23L; 143L; 101L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 1L;
    fuel = 9L;
    result_expected = 0x30ba5a04L;
  };
(*  
    call function_foo
    exit
    function_foo:
    mov r0, r10
    exit
    //ProgramResult::Ok(ebpf::MM_STACK_START (0x200000000) + config.stack_size() as u64),
*)
  {
    dis = "test_dynamic_stack_frames_empty";
    lp_std = [133L; 16L; 0L; 0L; 2L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 160L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 4L;
    result_expected = 8590196736L;
  };
(*  
    add r11, -8
    call function_foo
    exit
    function_foo:
    mov r0, r10
    exit
    //ProgramResult::Ok(ebpf::MM_STACK_START + config.stack_size() as u64 - 8),
*)
  {
    dis = "test_dynamic_frame_ptr_1";
    lp_std = [7L; 11L; 0L; 0L; 248L; 255L; 255L; 255L; 133L; 16L; 0L; 0L; 3L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 160L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 5L;
    result_expected = 8590196728L;
  };
(*
    add r11, -8
    call function_foo
    mov r0, r10
    exit
    function_foo:
    exit
*)
  {
    dis = "test_dynamic_frame_ptr_2";
    lp_std = [0x07L; 0x0bL; 0x00L; 0x00L; 0xf8L; 0xffL; 0xffL; 0xffL; 0x85L; 0x10L; 0x00L; 0x00L; 0x04L; 0x00L; 0x00L; 0x00L; 0xbfL; 0xa0L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 5L;
    result_expected = 8590196736L;
  };
(*
    entrypoint:
    call function_foo
    mov r0, 42
    exit
    function_foo:
    mov r0, 12
    exit
*)
  {
    dis = "test_entrypoint_exit";
    lp_std =  [133L; 16L; 0L; 0L; 3L; 0L; 0L; 0L; 183L; 0L; 0L; 0L; 42L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 0L; 0L; 0L; 12L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 5L;
    result_expected = 42L;
  };
(*
    call function_foo
    call function_foo
    exit
    function_foo:
    exit
*)
  {
    dis = "test_stack_call_depth_tracking";
    lp_std = [133L; 16L; 0L; 0L; 3L; 0L; 0L; 0L; 133L; 16L; 0L; 0L; 3L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 8L;
    result_expected = 0x0L;
  };
(*
    call function_foo
    call function_foo
    exit
    function_foo:
    exit
*)
  {
    dis = "test_bpf_to_bpf_depth";
    lp_std = [113L; 17L; 0L; 0L; 0L; 0L; 0L; 0L; 7L; 1L; 0L; 0L; 254L; 255L; 255L; 255L; 133L; 16L; 0L; 0L; 4L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 21L; 1L; 2L; 0L; 0L; 0L; 0L; 0L; 7L; 1L; 0L; 0L; 255L; 255L; 255L; 255L; 133L; 16L; 0L; 0L; 4L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [64L];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 254L;
    result_expected = 0x0L;
  };
(*
    mov64 r6, 0x11
    mov64 r7, 0x22
    mov64 r8, 0x44
    mov64 r9, 0x88
    call function_foo
    mov64 r0, r6
    add64 r0, r7
    add64 r0, r8
    add64 r0, r9
    exit
    function_foo:
    mov64 r6, 0x00
    mov64 r7, 0x00
    mov64 r8, 0x00
    mov64 r9, 0x00
    exit
*)
  {
    dis = "test_bpf_to_bpf_scratch_registers";
    lp_std = [0xb7L; 0x06L; 0x00L; 0x00L; 0x11L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x07L; 0x00L; 0x00L; 0x22L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x08L; 0x00L; 0x00L; 0x44L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x09L; 0x00L; 0x00L; 0x88L; 0x00L; 0x00L; 0x00L; 0x85L; 0x10L; 0x00L; 0x00L; 0x0aL; 0x00L; 0x00L; 0x00L; 0xbfL; 0x60L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x0fL; 0x70L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x0fL; 0x80L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x0fL; 0x90L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x06L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x07L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x08L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0xb7L; 0x09L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x95L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 15L;
    result_expected = 0xffL;
  };
(*
    ldxb r2, [r1+0xc]
    ldxb r3, [r1+0xd]
    lsh64 r3, 0x8
    or64 r3, r2
    mov64 r0, 0x0
    jne r3, 0x8, +0xc
    ldxb r2, [r1+0x17]
    jne r2, 0x6, +0xa
    ldxb r2, [r1+0xe]
    add64 r1, 0xe
    and64 r2, 0xf
    lsh64 r2, 0x2
    add64 r1, r2
    ldxh r2, [r1+0x2]
    jeq r2, 0x5000, +0x2
    ldxh r1, [r1+0x0]
    jne r1, 0x5000, +0x1
    mov64 r0, 0x1
    exit
*)
  {
    dis = "test_tcp_port80_match";
    lp_std = [113L; 18L; 12L; 0L; 0L; 0L; 0L; 0L; 113L; 19L; 13L; 0L; 0L; 0L; 0L; 0L; 103L; 3L; 0L; 0L; 8L; 0L; 0L; 0L; 79L; 35L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 85L; 3L; 12L; 0L; 8L; 0L; 0L; 0L; 113L; 18L; 23L; 0L; 0L; 0L; 0L; 0L; 85L; 2L; 10L; 0L; 6L; 0L; 0L; 0L; 113L; 18L; 14L; 0L; 0L; 0L; 0L; 0L; 7L; 1L; 0L; 0L; 14L; 0L; 0L; 0L; 87L; 2L; 0L; 0L; 15L; 0L; 0L; 0L; 103L; 2L; 0L; 0L; 2L; 0L; 0L; 0L; 15L; 33L; 0L; 0L; 0L; 0L; 0L; 0L; 105L; 18L; 2L; 0L; 0L; 0L; 0L; 0L; 21L; 2L; 2L; 0L; 0L; 80L; 0L; 0L; 105L; 17L; 0L; 0L; 0L; 0L; 0L; 0L; 85L; 1L; 1L; 0L; 0L; 80L; 0L; 0L; 183L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x00L; 0x01L; 0x02L; 0x03L; 0x04L; 0x05L; 0x00L; 0x06L; 
              0x07L; 0x08L; 0x09L; 0x0aL; 0x08L; 0x00L; 0x45L; 0x00L; 
              0x00L; 0x56L; 0x00L; 0x01L; 0x00L; 0x00L; 0x40L; 0x06L; 
              0xf9L; 0x4dL; 0xc0L; 0xa8L; 0x00L; 0x01L; 0xc0L; 0xa8L; 
              0x00L; 0x02L; 0x27L; 0x10L; 0x00L; 0x50L; 0x00L; 0x00L; 
              0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x50L; 0x02L; 
              0x20L; 0x00L; 0xc5L; 0x18L; 0x00L; 0x00L; 0x44L; 0x44L; 
              0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 
              0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 
              0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 
              0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 
              0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 
              0x44L; 0x44L; 0x44L; 0x44L];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 17L;
    result_expected = 0x01L;
  };
(*
    ldxb r2, [r1+0xc]
    ldxb r3, [r1+0xd]
    lsh64 r3, 0x8
    or64 r3, r2
    mov64 r0, 0x0
    jne r3, 0x8, +0xc
    ldxb r2, [r1+0x17]
    jne r2, 0x6, +0xa
    ldxb r2, [r1+0xe]
    add64 r1, 0xe
    and64 r2, 0xf
    lsh64 r2, 0x2
    add64 r1, r2
    ldxh r2, [r1+0x2]
    jeq r2, 0x5000, +0x2
    ldxh r1, [r1+0x0]
    jne r1, 0x5000, +0x1
    mov64 r0, 0x1
    exit
*)
  {
    dis = "test_tcp_port80_nomatch";
    lp_std = [113L; 18L; 12L; 0L; 0L; 0L; 0L; 0L; 113L; 19L; 13L; 0L; 0L; 0L; 0L; 0L; 103L; 3L; 0L; 0L; 8L; 0L; 0L; 0L; 79L; 35L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 85L; 3L; 12L; 0L; 8L; 0L; 0L; 0L; 113L; 18L; 23L; 0L; 0L; 0L; 0L; 0L; 85L; 2L; 10L; 0L; 6L; 0L; 0L; 0L; 113L; 18L; 14L; 0L; 0L; 0L; 0L; 0L; 7L; 1L; 0L; 0L; 14L; 0L; 0L; 0L; 87L; 2L; 0L; 0L; 15L; 0L; 0L; 0L; 103L; 2L; 0L; 0L; 2L; 0L; 0L; 0L; 15L; 33L; 0L; 0L; 0L; 0L; 0L; 0L; 105L; 18L; 2L; 0L; 0L; 0L; 0L; 0L; 21L; 2L; 2L; 0L; 0L; 80L; 0L; 0L; 105L; 17L; 0L; 0L; 0L; 0L; 0L; 0L; 85L; 1L; 1L; 0L; 0L; 80L; 0L; 0L; 183L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x00L; 0x01L; 0x02L; 0x03L; 0x04L; 0x05L; 0x00L; 0x06L; 
              0x07L; 0x08L; 0x09L; 0x0aL; 0x08L; 0x01L; 0x45L; 0x00L; 
              0x00L; 0x56L; 0x00L; 0x01L; 0x00L; 0x00L; 0x40L; 0x06L; 
              0xf9L; 0x4dL; 0xc0L; 0xa8L; 0x00L; 0x01L; 0xc0L; 0xa8L; 
              0x00L; 0x02L; 0x27L; 0x10L; 0x00L; 0x50L; 0x00L; 0x00L; 
              0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x50L; 0x02L; 
              0x20L; 0x00L; 0xc5L; 0x18L; 0x00L; 0x00L; 0x44L; 0x44L; 
              0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L;
              0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L;
              0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L;
              0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L;
              0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L;
              0x44L; 0x44L; 0x44L; 0x44L;];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 7L;
    result_expected = 0x0L;
  };
(*
    ldxb r2, [r1+0xc]
    ldxb r3, [r1+0xd]
    lsh64 r3, 0x8
    or64 r3, r2
    mov64 r0, 0x0
    jne r3, 0x8, +0xc
    ldxb r2, [r1+0x17]
    jne r2, 0x6, +0xa
    ldxb r2, [r1+0xe]
    add64 r1, 0xe
    and64 r2, 0xf
    lsh64 r2, 0x2
    add64 r1, r2
    ldxh r2, [r1+0x2]
    jeq r2, 0x5000, +0x2
    ldxh r1, [r1+0x0]
    jne r1, 0x5000, +0x1
    mov64 r0, 0x1
    exit
*)
  {
    dis = "test_tcp_port80_nomatch_proto";
    lp_std = [113L; 18L; 12L; 0L; 0L; 0L; 0L; 0L; 113L; 19L; 13L; 0L; 0L; 0L; 0L; 0L; 103L; 3L; 0L; 0L; 8L; 0L; 0L; 0L; 79L; 35L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 85L; 3L; 12L; 0L; 8L; 0L; 0L; 0L; 113L; 18L; 23L; 0L; 0L; 0L; 0L; 0L; 85L; 2L; 10L; 0L; 6L; 0L; 0L; 0L; 113L; 18L; 14L; 0L; 0L; 0L; 0L; 0L; 7L; 1L; 0L; 0L; 14L; 0L; 0L; 0L; 87L; 2L; 0L; 0L; 15L; 0L; 0L; 0L; 103L; 2L; 0L; 0L; 2L; 0L; 0L; 0L; 15L; 33L; 0L; 0L; 0L; 0L; 0L; 0L; 105L; 18L; 2L; 0L; 0L; 0L; 0L; 0L; 21L; 2L; 2L; 0L; 0L; 80L; 0L; 0L; 105L; 17L; 0L; 0L; 0L; 0L; 0L; 0L; 85L; 1L; 1L; 0L; 0L; 80L; 0L; 0L; 183L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x00L; 0x01L; 0x02L; 0x03L; 0x04L; 0x05L; 0x00L; 0x06L; 
              0x07L; 0x08L; 0x09L; 0x0aL; 0x08L; 0x01L; 0x45L; 0x00L; 
              0x00L; 0x56L; 0x00L; 0x01L; 0x00L; 0x00L; 0x40L; 0x06L; 
              0xf9L; 0x4dL; 0xc0L; 0xa8L; 0x00L; 0x01L; 0xc0L; 0xa8L; 
              0x00L; 0x02L; 0x27L; 0x10L; 0x00L; 0x50L; 0x00L; 0x00L; 
              0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x00L; 0x50L; 0x02L; 
              0x20L; 0x00L; 0xc5L; 0x18L; 0x00L; 0x00L; 0x44L; 0x44L; 
              0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L;
              0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L;
              0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L;
              0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L;
              0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L; 0x44L;
              0x44L; 0x44L; 0x44L; 0x44L;];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 9L;
    result_expected = 0x0L;
  };
(*
    ldxb r2, [r1+12]
    ldxb r3, [r1+13]
    lsh r3, 0x8
    or r3, r2
    mov r0, 0x0
    jne r3, 0x8, +37
    ldxb r2, [r1+23]
    jne r2, 0x6, +35
    ldxb r2, [r1+14]
    add r1, 0xe
    and r2, 0xf
    lsh r2, 0x2
    add r1, r2
    mov r0, 0x0
    ldxh r4, [r1+12]
    add r1, 0x14
    rsh r4, 0x2
    and r4, 0x3c
    mov r2, r4
    add r2, -20
    mov r5, 0x15
    mov r3, 0x0
    jgt r5, r4, +20
    mov r5, r3
    lsh r5, 0x20
    arsh r5, 0x20
    mov r4, r1
    add r4, r5
    ldxb r5, [r4]
    jeq r5, 0x1, +4
    jeq r5, 0x0, +12
    mov r6, r3
    jeq r5, 0x5, +9
    ja +2
    add r3, 0x1
    mov r6, r3
    ldxb r3, [r4+1]
    add r3, r6
    lsh r3, 0x20
    arsh r3, 0x20
    jsgt r2, r3, -18
    ja +1
    mov r0, 0x1
    exit
*)
  {
    dis = "test_tcp_sack_match";
    lp_std = [113L; 18L; 12L; 0L; 0L; 0L; 0L; 0L; 113L; 19L; 13L; 0L; 0L; 0L; 0L; 0L; 103L; 3L; 0L; 0L; 8L; 0L; 0L; 0L; 79L; 35L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 85L; 3L; 12L; 0L; 8L; 0L; 0L; 0L; 113L; 18L; 23L; 0L; 0L; 0L; 0L; 0L; 85L; 2L; 10L; 0L; 6L; 0L; 0L; 0L; 113L; 18L; 14L; 0L; 0L; 0L; 0L; 0L; 7L; 1L; 0L; 0L; 14L; 0L; 0L; 0L; 87L; 2L; 0L; 0L; 15L; 0L; 0L; 0L; 103L; 2L; 0L; 0L; 2L; 0L; 0L; 0L; 15L; 33L; 0L; 0L; 0L; 0L; 0L; 0L; 105L; 18L; 2L; 0L; 0L; 0L; 0L; 0L; 21L; 2L; 2L; 0L; 0L; 80L; 0L; 0L; 105L; 17L; 0L; 0L; 0L; 0L; 0L; 0L; 85L; 1L; 1L; 0L; 0L; 80L; 0L; 0L; 183L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x00L; 0x26L; 0x62L; 0x2fL; 0x47L; 0x87L; 0x00L; 0x1dL; 
              0x60L; 0xb3L; 0x01L; 0x84L; 0x08L; 0x00L; 0x45L; 0x00L; 
              0x00L; 0x40L; 0xa8L; 0xdeL; 0x40L; 0x00L; 0x40L; 0x06L;
              0x9dL; 0x58L; 0xc0L; 0xa8L; 0x01L; 0x03L; 0x3fL; 0x74L; 
              0xf3L; 0x61L; 0xe5L; 0xc0L; 0x00L; 0x50L; 0xe5L; 0x94L; 
              0x3fL; 0x77L; 0xa3L; 0xc4L; 0xc4L; 0x80L; 0xb0L; 0x10L; 
              0x01L; 0x3eL; 0x34L; 0xb6L; 0x00L; 0x00L; 0x01L; 0x01L; 
              0x08L; 0x0aL; 0x00L; 0x17L; 0x95L; 0x6fL; 0x8dL; 0x9dL; 
              0x9eL; 0x27L; 0x01L; 0x01L; 0x05L; 0x0aL; 0xa3L; 0xc4L; 
              0xcaL; 0x28L; 0xa3L; 0xc4L; 0xcfL; 0xd0L;];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 79L;
    result_expected = 0x01L;
  };
(*
    ldxb r2, [r1+12]
    ldxb r3, [r1+13]
    lsh r3, 0x8
    or r3, r2
    mov r0, 0x0
    jne r3, 0x8, +37
    ldxb r2, [r1+23]
    jne r2, 0x6, +35
    ldxb r2, [r1+14]
    add r1, 0xe
    and r2, 0xf
    lsh r2, 0x2
    add r1, r2
    mov r0, 0x0
    ldxh r4, [r1+12]
    add r1, 0x14
    rsh r4, 0x2
    and r4, 0x3c
    mov r2, r4
    add r2, -20
    mov r5, 0x15
    mov r3, 0x0
    jgt r5, r4, +20
    mov r5, r3
    lsh r5, 0x20
    arsh r5, 0x20
    mov r4, r1
    add r4, r5
    ldxb r5, [r4]
    jeq r5, 0x1, +4
    jeq r5, 0x0, +12
    mov r6, r3
    jeq r5, 0x5, +9
    ja +2
    add r3, 0x1
    mov r6, r3
    ldxb r3, [r4+1]
    add r3, r6
    lsh r3, 0x20
    arsh r3, 0x20
    jsgt r2, r3, -18
    ja +1
    mov r0, 0x1
    exit
*)
  {
    dis = "test_tcp_sack_nomatch";
    lp_std = [113L; 18L; 12L; 0L; 0L; 0L; 0L; 0L; 113L; 19L; 13L; 0L; 0L; 0L; 0L; 0L; 103L; 3L; 0L; 0L; 8L; 0L; 0L; 0L; 79L; 35L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 85L; 3L; 37L; 0L; 8L; 0L; 0L; 0L; 113L; 18L; 23L; 0L; 0L; 0L; 0L; 0L; 85L; 2L; 35L; 0L; 6L; 0L; 0L; 0L; 113L; 18L; 14L; 0L; 0L; 0L; 0L; 0L; 7L; 1L; 0L; 0L; 14L; 0L; 0L; 0L; 87L; 2L; 0L; 0L; 15L; 0L; 0L; 0L; 103L; 2L; 0L; 0L; 2L; 0L; 0L; 0L; 15L; 33L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 105L; 20L; 12L; 0L; 0L; 0L; 0L; 0L; 7L; 1L; 0L; 0L; 20L; 0L; 0L; 0L; 119L; 4L; 0L; 0L; 2L; 0L; 0L; 0L; 87L; 4L; 0L; 0L; 60L; 0L; 0L; 0L; 191L; 66L; 0L; 0L; 0L; 0L; 0L; 0L; 7L; 2L; 0L; 0L; 236L; 255L; 255L; 255L; 183L; 5L; 0L; 0L; 21L; 0L; 0L; 0L; 183L; 3L; 0L; 0L; 0L; 0L; 0L; 0L; 45L; 69L; 20L; 0L; 0L; 0L; 0L; 0L; 191L; 53L; 0L; 0L; 0L; 0L; 0L; 0L; 103L; 5L; 0L; 0L; 32L; 0L; 0L; 0L; 199L; 5L; 0L; 0L; 32L; 0L; 0L; 0L; 191L; 20L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 84L; 0L; 0L; 0L; 0L; 0L; 0L; 113L; 69L; 0L; 0L; 0L; 0L; 0L; 0L; 21L; 5L; 4L; 0L; 1L; 0L; 0L; 0L; 21L; 5L; 12L; 0L; 0L; 0L; 0L; 0L; 191L; 54L; 0L; 0L; 0L; 0L; 0L; 0L; 21L; 5L; 9L; 0L; 5L; 0L; 0L; 0L; 5L; 0L; 2L; 0L; 0L; 0L; 0L; 0L; 7L; 3L; 0L; 0L; 1L; 0L; 0L; 0L; 191L; 54L; 0L; 0L; 0L; 0L; 0L; 0L; 113L; 67L; 1L; 0L; 0L; 0L; 0L; 0L; 15L; 99L; 0L; 0L; 0L; 0L; 0L; 0L; 103L; 3L; 0L; 0L; 32L; 0L; 0L; 0L; 199L; 3L; 0L; 0L; 32L; 0L; 0L; 0L; 109L; 50L; 238L; 255L; 0L; 0L; 0L; 0L; 5L; 0L; 1L; 0L; 0L; 0L; 0L; 0L; 183L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [  0x00L; 0x26L; 0x62L; 0x2fL; 0x47L; 0x87L; 0x00L; 0x1dL; 
                0x60L; 0xb3L; 0x01L; 0x84L; 0x08L; 0x00L; 0x45L; 0x00L; 
                0x00L; 0x40L; 0xa8L; 0xdeL; 0x40L; 0x00L; 0x40L; 0x06L; 
                0x9dL; 0x58L; 0xc0L; 0xa8L; 0x01L; 0x03L; 0x3fL; 0x74L; 
                0xf3L; 0x61L; 0xe5L; 0xc0L; 0x00L; 0x50L; 0xe5L; 0x94L; 
                0x3fL; 0x77L; 0xa3L; 0xc4L; 0xc4L; 0x80L; 0x80L; 0x10L; 
                0x01L; 0x3eL; 0x34L; 0xb6L; 0x00L; 0x00L; 0x01L; 0x01L; 
                0x08L; 0x0aL; 0x00L; 0x17L; 0x95L; 0x6fL; 0x8dL; 0x9dL; 
                0x9eL; 0x27L];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 55L;
    result_expected = 0x0L;
  };
(*
    mov64 r0, 0x0
    mov64 r8, 0x1
    lsh64 r8, 0x20
    or64 r8, 0x30
    callx r8
    exit
    function_foo:
    mov64 r0, 0x2A
    exit
*)
  {
    dis = "test_callx";
    lp_std = [183L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 8L; 0L; 0L; 1L; 0L; 0L; 0L; 103L; 8L; 0L; 0L; 32L; 0L; 0L; 0L; 71L; 8L; 0L; 0L; 48L; 0L; 0L; 0L; 141L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 0L; 0L; 0L; 42L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 8L;
    result_expected = 0x2aL;
  };
(*
    mov64 r0, 0x0
    mov64 r8, 0x1
    lsh64 r8, 0x20
    or64 r8, 0x30
    callx r8
    exit
    function_foo:
    mov64 r0, 0x2A
    exit
*)
  {
    dis = "test_callx_imm";
    lp_std = [183L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 8L; 0L; 0L; 1L; 0L; 0L; 0L; 103L; 8L; 0L; 0L; 32L; 0L; 0L; 0L; 71L; 8L; 0L; 0L; 48L; 0L; 0L; 0L; 141L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 0L; 0L; 0L; 42L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 8L;
    result_expected = 0x2aL;
  };
(*
    call function_c
    exit
    function_a:
    exit
    function_b:
    .fill 1024, 0x0F
    exit
    function_c:
    mov32 r1, 0x00000010
    hor64 r1, 0x00000001
    callx r1
    exit
*)
  {
    dis = "test_far_jumps";
    lp_std = [133L; 16L; 0L; 0L; 4L; 4L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 180L; 1L; 0L; 0L; 16L; 0L; 0L; 0L; 247L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 141L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = true;
    v = 2L;
    fuel = 7L;
    result_expected = 0x0L;
  };
(*
    ldxdw r0, [r1+6]
    exit
*)
  {
    dis = "test_err_ldxdw_oob";
    lp_std = [121L; 16L; 6L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0xaaL; 0xbbL; 0x11L; 0x22L; 0x33L; 0x44L; 0x55L; 0x66L; 0x77L; 0x88L; 0xccL; 0xddL;];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 1L;
    result_expected = 0x0L;
  };
(*
    mov32 r0, 1
    mov32 r7, 0
    mod32 r0, r7
    exit
*)
  {
    dis = "test_divide_by_zero_1";
    lp_std = [180L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 180L; 7L; 0L; 0L; 0L; 0L; 0L; 0L; 156L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 3L;
    result_expected = 0x0L;
  };
(*
    mov32 r0, 1
    mov32 r1, 0
    mod r0, r1
    exit
*)
  {
    dis = "test_divide_by_zero_2";
    lp_std = [180L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 180L; 1L; 0L; 0L; 0L; 0L; 0L; 0L; 159L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 3L;
    result_expected = 0x0L;
  };
  (*
    mov32 r0, 1
    mov32 r1, 0
    div r0, r1
    exit
*)
  {
    dis = "test_divide_by_zero_3";
    lp_std = [180L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 180L; 1L; 0L; 0L; 0L; 0L; 0L; 0L; 63L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 3L;
    result_expected = 0x0L;
  };
(*
    mov32 r0, 1
    mov32 r1, 0
    div32 r0, r1
    exit
*)
  {
    dis = "test_divide_by_zero_4";
    lp_std = [180L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 180L; 1L; 0L; 0L; 0L; 0L; 0L; 0L; 60L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 3L;
    result_expected = 0x0L;
  };
(*
    mov r0, 0
    lddw r1, 0x1
    mov r2, 0
    exit
*)
{
  dis = "test_lddw_err_exceeded_1";
  lp_std = [183L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 24L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 2L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
  lm_std = [];
  lc_std = [];
  isok = false;
  v = 1L;
  fuel = 2L;
  result_expected = 0x0L;
};
(*
    lddw r1, 0x100000038
    callx r1
    mov r0, r0
    mov r0, r0
    exit
    lddw r0, 0x1122334455667788
    exit
*)
  {
    dis = "test_lddw_err_unsupport_1";
    lp_std = [24L; 1L; 0L; 0L; 56L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 141L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 24L; 0L; 0L; 0L; 136L; 119L; 102L; 85L; 0L; 0L; 0L; 0L; 68L; 51L; 34L; 17L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 1L;
    fuel = 3L;
    result_expected = 0x0L;
  };
(*
    mov64 r1, 0x1
    lsh64 r1, 0x20
    or64 r1, 0x38
    callx r1
    mov r0, r0
    mov r0, r0
    lddw r0, 0x1122334455667788
    exit
*)
  {
    dis = "test_lddw_err_unsupport_2";
    lp_std = [183L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 103L; 1L; 0L; 0L; 32L; 0L; 0L; 0L; 71L; 1L; 0L; 0L; 56L; 0L; 0L; 0L; 141L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 24L; 0L; 0L; 0L; 136L; 119L; 102L; 85L; 0L; 0L; 0L; 0L; 68L; 51L; 34L; 17L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 1L;
    fuel = 5L;
    result_expected = 0x0L;
  };
(*
    mov64 r8, 0x1
    lsh64 r8, 0x20
    or64 r8, 0x28
    callx r8
    lddw r0, 0x1122334455667788
    exit
*)
  {
    dis = "test_lddw_err_unsupport_3";
    lp_std = [183L; 8L; 0L; 0L; 1L; 0L; 0L; 0L; 103L; 8L; 0L; 0L; 32L; 0L; 0L; 0L; 71L; 8L; 0L; 0L; 40L; 0L; 0L; 0L; 141L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 24L; 0L; 0L; 0L; 136L; 119L; 102L; 85L; 0L; 0L; 0L; 0L; 68L; 51L; 34L; 17L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 1L;
    fuel = 5L;
    result_expected = 0x0L;
  };
(*
    mov64 r8, 0x1
    lsh64 r8, 0x20
    or64 r8, 0x28
    callx r8
    lddw r0, 0x1122334455667788
    exit
*)
  {
    dis = "test_lddw_err_exceeded_2";
    lp_std = [183L; 8L; 0L; 0L; 1L; 0L; 0L; 0L; 103L; 8L; 0L; 0L; 32L; 0L; 0L; 0L; 71L; 8L; 0L; 0L; 40L; 0L; 0L; 0L; 141L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 24L; 0L; 0L; 0L; 136L; 119L; 102L; 85L; 0L; 0L; 0L; 0L; 68L; 51L; 34L; 17L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 1L;
    fuel = 4L;
    result_expected = 0x0L;
  };
(*
    stb [r10-0x4000], 0
    exit
*)
  {
    dis = "test_err_fixed_stack_out_of_bound";
    lp_std = [114L; 10L; 0L; 192L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 1L;
    fuel = 1L;
    result_expected = 0x0L;
  };
  (*
    mov64 r1, 0x1
    lsh64 r1, 0x20
    or64 r1, 0x28
    callx r1
    exit
    function_foo:
    exit
*)
  {
    dis = "test_err_exit_capped_1";
    lp_std = [183L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 103L; 1L; 0L; 0L; 32L; 0L; 0L; 0L; 71L; 1L; 0L; 0L; 40L; 0L; 0L; 0L; 141L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 5L;
    result_expected = 0x0L;
  };
(*
    mov64 r1, 0x1
    lsh64 r1, 0x20
    or64 r1, 0x28
    callx r1
    exit
    function_foo:
    mov r0, r0
    exit
*)
  {
    dis = "test_err_exit_capped_2";
    lp_std = [183L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 103L; 1L; 0L; 0L; 32L; 0L; 0L; 0L; 71L; 1L; 0L; 0L; 40L; 0L; 0L; 0L; 141L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 6L;
    result_expected = 0x0L;
  };
(*
    call 1
    exit
    mov r0, r0
    exit
*)
  {
    dis = "test_err_exit_capped_3";
    lp_std = [133L; 16L; 0L; 0L; 2L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 3L;
    result_expected = 0x0L;
  };
(*
    mov64 r1, 0x0
    mov64 r2, 0x0
    add64 r0, 0x0
    add64 r0, 0x0
    udiv64 r1, r2
    add64 r0, 0x0
    exit
*)
  {
    dis = "test_err_capped_before_exception_1";
    lp_std = [183L; 1L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 2L; 0L; 0L; 0L; 0L; 0L; 0L; 7L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 7L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 94L; 33L; 0L; 0L; 0L; 0L; 0L; 0L; 7L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 4L;
    result_expected = 0x0L;
  };
(*
    mov64 r1, 0x0
    mov64 r2, 0x0
    add64 r0, 0x0
    add64 r0, 0x0
    callx r2
    add64 r0, 0x0
    exit
*)
  {
    dis = "test_err_capped_before_exception_2";
    lp_std = [183L; 1L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 2L; 0L; 0L; 0L; 0L; 0L; 0L; 7L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 7L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 141L; 32L; 0L; 0L; 0L; 0L; 0L; 0L; 7L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 4L;
    result_expected = 0x0L;
  };
(*
    mov64 r1, 0x0
    mov64 r2, 0x0
    add64 r0, 0x0
    add64 r0, 0x0
    callx r2
    add64 r0, 0x0
    exit
*)
  {
    dis = "test_non_terminate_early";
    lp_std = [183L; 6L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 1L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 2L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 3L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 4L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 101L; 0L; 0L; 0L; 0L; 0L; 0L; 141L; 96L; 0L; 0L; 0L; 0L; 0L; 0L; 7L; 6L; 0L; 0L; 1L; 0L; 0L; 0L; 5L; 0L; 248L; 255L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 7L;
    result_expected = 0x0L;
  };
(*
    mov64 r8, 0x1
    lsh64 r8, 0x20
    or64 r8, 0x28
    call function_foo
    exit
    function_foo:
    mov64 r3, 0x41414141
    callx r8
    exit
*)
  {
    dis = "test_tight_infinite_recursion_callx";
    lp_std = [183L; 8L; 0L; 0L; 1L; 0L; 0L; 0L; 103L; 8L; 0L; 0L; 32L; 0L; 0L; 0L; 71L; 8L; 0L; 0L; 40L; 0L; 0L; 0L; 133L; 16L; 0L; 0L; 5L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 3L; 0L; 0L; 65L; 65L; 65L; 65L; 141L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 8L;
    result_expected = 0x0L;
  };
(*
    entrypoint:
    mov64 r3, 0x41414141
    call entrypoint
    exit
*)
  {
    dis = "test_tight_infinite_recursion";
    lp_std = [183L; 3L; 0L; 0L; 65L; 65L; 65L; 65L; 133L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 4L;
    result_expected = 0x0L;
  };
(*
    jsge r0, r0, -1
    exit
*)
  {
    dis = "test_tight_infinite_loop_conditional";
    lp_std = [125L; 0L; 255L; 255L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 4L;
    result_expected = 0x0L;
  };
(*
    ja -1
    exit
*)
  {
    dis = "test_tight_infinite_loop_unconditional";
    lp_std = [5L; 0L; 255L; 255L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 4L;
    result_expected = 0x0L;
  };
(*
    mov64 r0, 0x1
    lsh64 r0, 0x20
    callx r0
    exit
*)
  {
    dis = "test_err_reg_stack_depth";
    lp_std = [183L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 103L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 141L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 192L;
    result_expected = 0x0L;
  };
(*
    ldxb r1, [r1]
    add64 r1, -2
    call function_foo
    exit
    function_foo:
    jeq r1, 0, +2
    add64 r1, -1
    call function_foo
    exit
*)
  {
    dis = "test_bpf_to_bpf_depth_err";
    lp_std = [113L; 17L; 0L; 0L; 0L; 0L; 0L; 0L; 7L; 1L; 0L; 0L; 254L; 255L; 255L; 255L; 133L; 16L; 0L; 0L; 4L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 21L; 1L; 2L; 0L; 0L; 0L; 0L; 0L; 7L; 1L; 0L; 0L; 255L; 255L; 255L; 255L; 133L; 16L; 0L; 0L; 4L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 192L;
    result_expected = 0x0L;
  };
(*
    mov64 r0, 0x0
    mov64 r8, 0x1
    lsh64 r8, 0x20
    or64 r8, 0x30
    callx r8
    exit
    mov64 r0, 0x2A
    exit
*)
  {
    dis = "test_err_callx_unregistered";
    lp_std = [183L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 8L; 0L; 0L; 1L; 0L; 0L; 0L; 103L; 8L; 0L; 0L; 32L; 0L; 0L; 0L; 71L; 8L; 0L; 0L; 48L; 0L; 0L; 0L; 141L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 0L; 0L; 0L; 42L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 6L;
    result_expected = 0x0L;
  };
(*
    mov64 r0, 0x3
    callx r0
    exit
*)
  {
    dis = "test_err_callx_oob_low";
    lp_std = [183L; 0L; 0L; 0L; 3L; 0L; 0L; 0L; 141L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 2L;
    result_expected = 0x0L;
  };

(*
    entrypoint:
    call function_foo
    exit
    function_foo:
    call function_bar
    exit
    function_bar:
    exit
*)
  {
    dis = "test_stack_call_depth_tracking_err";
    lp_std = [133L; 16L; 0L; 0L; 2L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 133L; 16L; 0L; 0L; 4L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 2L;
    result_expected = 0x0L;
  };
(*
    add r11, -0x7FFFFFFF
    add r11, -0x7FFFFFFF
    add r11, -0x7FFFFFFF
    add r11, -0x7FFFFFFF
    add r11, -0x40005
    call function_foo
    exit
    function_foo:
    stb [r10], 0
    exit
*)
  {
    dis = "test_err_dynamic_stack_ptr_overflow";
    lp_std = [7L; 11L; 0L; 0L; 1L; 0L; 0L; 128L; 7L; 11L; 0L; 0L; 1L; 0L; 0L; 128L; 7L; 11L; 0L; 0L; 1L; 0L; 0L; 128L; 7L; 11L; 0L; 0L; 1L; 0L; 0L; 128L; 7L; 11L; 0L; 0L; 251L; 255L; 251L; 255L; 133L; 16L; 0L; 0L; 7L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 114L; 10L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 7L;
    result_expected = 0x0L;
  };
(*
    stb [r10-0x3001], 0
    exit
*)
  {
    dis = "test_err_dynamic_stack_out_of_bound";
    lp_std =  [114L; 10L; 255L; 207L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 1L;
    result_expected = 0x0L;
  };
(*
    stb [r10], 0
    exit
*)
  {
    dis = "test_err_dynamic_stack_out_of_bound";
    lp_std = [114L; 10L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 1L;
    result_expected = 0x0L;
  };
(*
    exit
*)
  {
    dis = "test_exit_capped";
    lp_std = [149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 0L;
    result_expected = 0x0L;
  };
(*
    ldxdw r0, [r1+6]
    exit
*)
  {
    dis = "test_err_ldxdw_nomem";
    lp_std = [121L; 16L; 6L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    isok = false;
    v = 2L;
    fuel = 1L;
    result_expected = 0x0L;
  };
(*
    ldxdw r0, [r1+6]
    exit
*)
{
  dis = "test_err_ldxdw_oob";
  lp_std = [121L; 16L; 6L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
  lm_std = [0xaaL; 0xbbL; 0x11L; 0x22L; 0x33L; 0x44L; 0x55L; 0x66L; 0x77L; 0x88L; 0xccL; 0xddL];
  lc_std = [];
  isok = false;
  v = 2L;
  fuel = 1L;
  result_expected = 0x0L;
};
]

let () =
  List.iter run_test_case test_cases;  
  Printf.printf "\nSummary:\n";
  Printf.printf "%sPassed: %d%s\n" green !passed reset;
  Printf.printf "%sFailed: %d%s\n" red !failed reset
  
  (*
  mov64 r0, -0x1
  lsh64 r0, 0x20
  or64 r0, 0x3
  callx r0
  exit

{
  dis = "test_err_callx_oob_high";
  lp_std = [183L; 0L; 0L; 0L; 255L; 255L; 255L; 255L; 103L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 71L; 0L; 0L; 0L; 3L; 0L; 0L; 0L; 141L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
  lm_std = [];
  lc_std = [];
  isok = false;
  v = 2L;
  fuel = 4L;
  result_expected = 0x0L;
};*)