# formal semantics of Solana eBPF ISA in Isabelle/HOL

The repo is a minimal copy of the [CertSBF](https://github.com/shenghaoyuan/CertSBF)

Note that we only test our project on
- Windows 11 + WSL2 (Ubuntu 22.04 LTS)
- Ubuntu 22.04 LTS

plus `CPU: Intel(R) Core(TM) Ultra 7 155H   1.40 GHz` + `RAM 32G` + `Core: 16`

# 1. SBPF ISA Semantics in Isabelle/HOL
## 1.1 Install Isabelle/HOL and AFP
- [Isabelle/HOL 2024](https://isabelle.in.tum.de/) (please set your PATH with e.g. `/YOUR-PATH/Isabelle2024`)

- [Isabelle AFP](https://www.isa-afp.org/download/) (unzip the AFP to your PATH, e.g. `/YOUR-PATH/afp`)

```shell
# set PATH 
vim  ~/.bashrc # export PATH=$PATH:/YOUR-PATH/Isabelle2024/bin:...
source ~/.bashrc

# test isabelle/hol
isabelle version # Isabelle2024

# config AFP
cd /YOUR-PATH/afp/thys
isabelle components -u . # Add AFP to ...

# go to our repo folder and open this project in jedit
cd /OUR-REPO

# adding the following libs when install on WSL2 with Ubuntu 22.04.3 LTS (GNU/Linux 5.15.153.1-microsoft-standard-WSL2 x86_64)
sudo apt-get install libxi6 libxtst6 libxrender1 fontconfig
```

## 1.2 Check the SBPF ISA semantics
This command starts up the IDE of Isabelle/HOL (JEdit), opens the `Interpreter.thy` file, and checks the semantics automatically.
```shell
make
```
If you want to check another file, just click it on JEdit and the Isabelle/HOL checker then validates it automatically.