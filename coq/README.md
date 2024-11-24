# Formal semantics of Solana eBPF ISA in Coq

  
## Installation

1. OPAM
```shell
# install opam
add-apt-repository ppa:avsm/ppa
apt update
apt install opam

# install ocaml+coq by opam
opam init
# install ocaml
opam switch create bpf ocaml-base-compiler.4.11.1

eval $(opam env)

# It is better to restart your computer/VM to flash the enviroment, Important !!!

opam switch list
#   switch  compiler      description
->  bpf     ocaml.4.11.1  bpf

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

```
2. Build CompCert
```shell
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


## How to run this Coq project

```shell
# go to the root folder of this repo
./configure --opamprefixdir=$OPAM_SWITCH_PREFIX --compcertdir=$COQPATH/compcert

make all
```
