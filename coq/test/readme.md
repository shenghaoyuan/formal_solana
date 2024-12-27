# (Int64.eq pc1 ipc) exist question that pc1 is positive and ipc is nagetive although their value is corresopnd. We find that it is because the function eq_dec which compare two value based on their sign. In the meanwhile, when Int64.one is positive, pc is Z0 and offset is negtive,their added result is positive although the real value is negtive which makes the compare of two same value is false.

# Refer to address in compcert, there exists a vmaddress which needs block and computing offset. However, because of the address provided by testcase is offset, we modified the rule of obtaining address from computing offset to applying provided address as offset directlt. Some day we may correct the logic of code.

# The unique testcase is abbow:
	[
	  {
	    "dis": "srem64 r1, 10",
	    "lp_std": [
	      "0x0000000A000001F6"
	    ],
	    "lr_std": [
	      "0x0000000000000000",
	      "0xFFFFFFFFFFFFFFF5",
	      "0xD83D3C9B1F016392",
	      "0xD72339E166BF87B1",
	      "0xF6C0077AE5505213",
	      "0x4C16E671E68FB587",
	      "0x9584A6A2F14DEAA6",
	      "0x50E05FAA744CD33C",
	      "0xFA221AC4208BB99B",
	      "0x4AA6E05CD7A8D608"
	    ],
	    "lm_std": [],
	    "lc_std": [],
	    "v": "0x2",
	    "fuel": "0x1",
	    "index": "0x1",
	    "ipc": "0x1",
	    "result_expected": "0xFFFFFFFFFFFFFFFF"
	  }
	]
	
# note: Sometimes, you need to run `eval $(opam env)` before run `make compile`
