# Two Mechanizations of Solana eBPF instruction set architecture



## 1. Introduction

The artifact contains the code, formal proof and tests of our eBPF instruction set architecture for Solana.

1. We begin with a complete formal semantics of the Solana eBPF bytecode in Isabelle/HOL and coq, which facilitates the formalization of the eBPF interpreter.
2. We also introduce a validation framework that extracts the executable semantics from our formalization to OCaml language in both sides and test them against the original implementation of the Solana eBPF interpreter. The artifact includes the extracted code along with the glue code in OCaml, as well as over 100,000 micro-benchmarks and the Solana test suite for macro-benchmarks. Use `make micro-test` and `make macro-test` to compile and run the tests.

As claimed in Section 1.2 of our paper, the contributions of this paper include:

- Two Mechanizations of Complete Semantics of Solana eBPF ISA,
- Semantics Validation Framework.



## 2. Hardware Dependencies

Note that we only test our project on

- Windows 11 + WSL2 (Ubuntu 22.04 LTS)
- Ubuntu 22.04 LTS

plus `CPU: Intel(R) Core(TM) Ultra 7 155H   3.60 GHz` + `RAM 16G` + `Core: 8`



## 3. Getting Started Guide

Welcome to the SBPF ISA Semantics and Validation Framework! This guide will help you set up the necessary environment within approximately 5 minutes.

### 3.1 Set up

- **[Isabelle/HOL 2024](https://isabelle.in.tum.de/)**
  - Installation Path: `/YOUR-PATH/Isabelle2024`

- **[Isabelle AFP](https://www.isa-afp.org/download/) (Archive of Formal Proofs)** 
  - Installation Path: `/YOUR-PATH/afp`

```shell
# set isabelle PATH and update shell environment
vim  ~/.bashrc # export PATH=$PATH:/YOUR-PATH/Isabelle2024/bin:...
source ~/.bashrc

# test isabelle/hol
isabelle version # Isabelle2024

# config AFP
cd /YOUR-PATH/afp/thys
isabelle components -u . # Add AFP to ...

# go to our repo folder and open this project in jedit
cd /OUR-REPO
```

- **Rust**
  - Installation Instructions: [Rust Installation](https://www.rust-lang.org/tools/install)
  - For our environment:

```shell
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

rustc --version
# rustc 1.85.0
```

- **OCaml, Coq, Compcert and Related Packages**

```shell
# install opam

sudo apt install opam
# In the case you fail to install opam
# Note1: you may need the two commands before install opam, i.e. `add-apt-repository ppa:avsm/ppa` and `apt update`
# Note2: you may need to change your source list to focal source if `add-apt-repository ppa:avsm/ppa` fails


# install ocaml+coq by opam
opam init
# install ocaml
opam switch create sbpf ocaml-base-compiler.4.14.1 

eval $(opam env)

opam switch list
#   switch  compiler      description
->  sbpf     ocaml.4.14.1  sbpf

# Note3: Once you get a warning here, please do `eval $(opam env)`, restart your computer/VM, and do `eval $(opam env)` again

# make sure your ocaml is 4.14.1 and from `/home/bob/.opam/sbpf/bin/ocaml`
which ocaml

# install necessary packages
opam install ocamlfind yojson
```
  
- **[Coq](https://https://coq.inria.fr/download)** 
  - Installation Path: `/YOUR-PATH/Coq`


- **[CompCert](https://compcert.org/download.html)** 
  - Installation Path: `/YOUR-PATH/CompCert`



```shell
# Once you get a warning, please do `eval $(opam env)` and restart your computer/VM

# make sure your ocaml is 4.11.1 and from `/home/bob/.opam/bpf/bin/ocaml`
which ocaml

# install coq, etc.
opam repository add coq-released https://coq.inria.fr/opam/released

# install coq etc (optional: and coqide)
opam install coq.8.13.2 coq-elpi.1.11.0 coqide.8.13.2

# optional: install headache
# `opam install depext`
# `opam depext headache`
# `opam install headache`

# download CompCert from https://github.com/AbsInt/CompCert

opam repo add coq-released https://coq.inria.fr/opam/released
# install coq-flocq.4.1.0
opam install coq-flocq.4.1.0

# you may need a old menhir
opam install menhir.20210419

# install CompCert
cd YOUR_DIR/CompCert/compcert/
./configure x86_64-linux -use-external-Flocq -clightgen
make all

# set COQPATH
# Important: if you recompile CompCert again, remember to comment COQPATH firstly!!!
vim /home/bob/.bashrc
# adding the line `export COQPATH="YOUR_DIR/CompCert"`
source /home/bob/.bashrc
```


- **Cloc Tool**

```shell
sudo apt-get install cloc
```

- **Additional Libraries (for WSL2 users)**

```shell
sudo apt install libxi6 libxtst6 libxrender1 fontconfig
```

### 3.2 Basic Testing

Since we use the `Make` tool to build and manage the entire project, the basic testing process is quite straightforward with `make`.  Please refer to the **Step by Step Instructions** section for guidance.



## 4. Step by Step Instructions

This section provides detailed instructions to reproduce the experiments and activities that support the conclusions in our paper.

### 4.1 SBPF ISA Semantics

#### 4.1.1 Check the SBPF ISA semantics

- This command starts up the IDE of Isabelle/HOL (JEdit) or Coq proof, opens the `Interpreter.thy` or `Interpreter.v` file, and checks the semantics automatically.

```shell
# Go to the root directory of this repo
make
```

#### 4.1.2 Link to paper

| Paper                       | Code                                                         |
| --------------------------- | ------------------------------------------------------------ |
| Syntax (Section 4.1)        | `isabelle/theory/rBPFSyntax.thy#L41`  `coq/model/rBPFSyntax.v#L102`   |
| Semantics (Section 4.2)     | `isabelle/theory/Interpreter.thy#L510`   `isabelle/theory/Interpreter.thy#L608`    `coq/model/v.Interpreter#654`    `coq/model/v.Interpreter#773`        |

### 4.2 Solana VM applications

#### 4.2.1 Solana Assembler and Disassembler (Section 4.3 4.4)

| Paper                               | Code                             |
| ----------------------------------- | -------------------------------- |
| Solana Assembler                    | `isabelle/theory/Assembler.thy#L227`      `coq/model/rBPFEncoder.v#L19`    |
| Solana Disassembler                 | `isabelle/theory/Disassembler.thy#L515`     `coq/modelheory/rBPFDncoder.v#L516`  |
| Consistency Proof (Section 4.3 4.3) | `isabelle/theory/ConsistencyProof.thy#L8`    `coq/model/ConsistencyProof1.v#L9`   `coq/model/ConsistencyProof2.v#L7`|


### 4.3 Semantics Validation

- We have two sets of benchmarks for validating semantics:

  - **`Macro-test`**: Compiles and runs program-level tests using the Solana official test suite in `test/rbpf/tests/execution.rs`.

  - **`Micro-test`**: Compiles and runs instruction-level tests using the generated cases (100 tests by default).

```shell
# Go to the root directory of this repo
make macro-test
make micro-test
```

- (Optional)  We also provide **`make generator num=X`** to generate X random instruction test cases. 

```shell
# Go to the root directory of this repo
# For example, to generate and run 100000 tests
make generator num=100000
make micro-test
```

#### 4.3.1 Link to paper

| Paper                            | Code                                                         |
| -------------------------------- | ------------------------------------------------------------ |
| Validation Framework (Section 5) | isabell/hol: glue code1 `isabelle/theory/Interpreter.thy#L651` + glue code2 `isabelle/theory/Interpreter.thy#L683` + extraction declration `isabelle/theory/bpf_generator.thy#L15`, OCaml: glue code `test/exec_semantics/isabelle_test/glue.ml`, interpreter_test `test/exec_semantics/isabelle_test/interp_test.ml`, step_test `tests/exec_semantics/isabelle_test/step_test.ml`                                                coq: glue code1 `coq/model/Interpreter.v#L822` + glue code2 `coq/model/Interpreter.v#L848` + extraction declration `test/exec_semantics/coq_test/extract.v#L48`, OCaml: glue code `test/exec_semantics/coq_test/glue.ml`, interpreter_test `test/exec_semantics/coq_test/interpreter_test.ml`, step_test `test/exec_semantics/coq_test/step_test.ml`| 



## 5. Reusability Guide

### 5.1 Formalization
We show three examples for reusing our formal syntax and semantics.
### 5.1.1 Syntax

The formal syntax of our model could be used for other static analysis, for example, translating the Solana bytecode into CFG ( control flow graph) for further optimizations.
```ocaml
(* .coq/model/rBPFSyntax.v *)
Inductive bpf_instruction = 
  BPF_LD_IMM            dst_ty imm_ty imm_ty | 
  (* BPF_LDX class *)
  BPF_LDX memory_chunk  dst_ty src_ty off_ty |
  (* BPF_ST/BPF_STX class *)
  BPF_ST  memory_chunk  dst_ty snd_op off_ty |
  ...
```

### 5.1.2 Semantics
The formal semantics of our model could be used for other verification, for example, consider verified compilers from other high-level languages (e.g., C or Rust) to Solana bytecode, or from Solana bytecode to other target architectures (e.g., ARM or RISC-V).

```ocaml
(* ./coq/model/Interpreter.v *)
fun step :: "u64 ⇒ bpf_instruction ⇒ reg_map ⇒ mem ⇒ stack_state ⇒ SBPFV ⇒
  func_map ⇒ bool ⇒ int64 ⇒ int64 ⇒ int64 ⇒ block ⇒ bpf_state" where
  ...

fun bpf_interp :: "nat ⇒ bpf_bin ⇒ bpf_state ⇒ bool ⇒ int64 ⇒ block ⇒ bpf_state" where
...
```



### 5.2 Validation Framework

#### 5.2.1 Glue Code (Section 5.2)

- The glue code we integrate into the executable semantics at the OCaml layer is designed to be adaptable to similar use cases. This is because Isabelle/HOL automatically translates the `Word` library into an unambiguous format, which is **not human-readable** but consistent.
- We introduce the following functions to convert the OCaml code extracted by Isabelle/HOL into a usable form: 
  - **int_of_standard_int / int_list_of_standard_int_list**: These functions convert the native `int64` / `int64 list` types from the OCaml standard library to the `int` / `int list` types (we call it `myint`) generated by Isabelle/HOL.
  - **int64_to_z / int64_list_of_z_list**: These functions convert the native `int64` / `int64 list` types from the OCaml standard library to the `z` / `z list` types generated by Coq.
  - **bpf_interp_test**: This function offers a user-friendly interface for testing, using only `int`-related types. This simplifies the testing process by avoiding the need to input other data types.


```ocaml
(* ./test/exec_semantics/isabelle_test/interp_test.ml *)
val int_of_standard_int : int64 -> myint
val int_list_of_standard_int_list : int64 list -> myint list
val bpf_interp_test : int64 int -> int64 list ...

(* ./test/exec_semantics/icoq_test/interpreter_test.ml *)
val z_to_int64 : int64 -> z
val int64_list_of_z_list : int64 list -> z list
val bpf_interp_test : int64 int -> int64 list ...

(* ./tests/exec_semantics/isabelle_test/test.ml *)
open Interp_test

(* ./tests/exec_semantics/coq_test/test.ml *)
open Interpreter_test

let lp = Interp_test.int_list_of_standard_int_list test_case.lp_std in
let lm = Interp_test.int_list_of_standard_int_list test_case.lm_std in  
...
let result = Interp_test.bpf_interp_test lp lm ..
```



#### 5.2.2 Customize Test Cases

- To run customized program-level tests, you can navigate to `./test/exec_semantics/isabelle_test/test.ml` or `./test/exec_semantics/coq_test/test.ml`, and add your own test. The following example outlines the structure of a test case:
  - **SBPF Binary Code**: A list of bytes, generated by the Solana rbpf assembler.
  - **Memory Region**: A list of bytes that maps from an `int64` address to a byte.
  - **Syscall Interface**: A list of bytes, though not used in this case since we don't consider test cases involving system calls.
  - **Test Result**: `true` for normal tests and `false` for expectation tests.
  - **SBPF Instruction Version**: Either 1 or 2.
  - **Instruction Count**: The number of instructions executed.
  - **Expected Result**: The result generated by the Solana rbpf after running the test case.


```ocaml 
let test_cases = [
  (*
    / sbpf assembly code
    mov32 r1, 1
    mov32 r0, r1
    exit
  *)
  {
    dis = "test_mov";                            (* Description of the test *)
    lp_std = [180L; 1L; 0L; 0L; 1L; 0L; 0L; 0L;   (* SBPF binary code *)
              188L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 
              149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];                                 (* Memory region *)
    lc_std = [];                                 (* Syscall interface, not used here *)
    isok = true;                                 (* Test result: true for normal tests *)
    v = 2L;                                      (* SBPF instruction version *)
    fuel = 3L;                                   (* Instruction count *)
    result_expected = 0x01L;                     (* Expected result *)
  };
]
```

- To run customized instruction-level tests, you can navigate to `./tests/data/ocaml_in.json` and add your own test. To avoid redundancy, we will focus on explaining the parts that differ from program-level tests:
  - **Register Map**: A randomly generated `int64` SBPF register map from `r0` to `r9`. Note that `r0` is always set to `0` for special instructions (e.g., memory load), which need an extra register to store the return result.
  - **Destination register**: The register where the test result is stored.
  - **Program counter**: The final state of the Program Counter (PC) register.

```json
  {
    "dis": "div r2, 1602358370",							// Description of the test
    "lp_std": [												// SBPF binary code
      "0x37","0x01","0x00","0x00",
      "0x62","0x0C","0x82","0x5F"
    ],
    "lr_std": [												// Register Map
      "0x0000000000000000",
      "0xF4E4C7CAC29A21B8",
      "0x6A5B61236C67D43F",
      "0x5F7B322164C7AF21",
      "0x19FD779B6887B44B",
      "0xA292FCF87FCCC5AC",
      "0x9035EE5D8AF15E0B",
      "0x569AFA5E4607F42C",
      "0x1B5ED1DC1AADE3E0",
      "0x4B0A8B676C7BCF0C"
    ],
    "lm_std": [],											// Memory Region
    "lc_std": [],											// Syscall interface
    "v": "0x1",												// SBPF instruction version
    "fuel": "0x1",											// Instruction count
    "index": "0x2",											// Destination register 
    "ipc": "0x1",											// Program counter
    "result_expected": "0x29069F5D9"						// Expected result
  },
```
