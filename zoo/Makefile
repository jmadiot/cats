# models=sc_nosm tso_nosm x86tso

all: zoo.vo tso_nosm.v x86tso.v sc_nosm.v rc11.v

x86tso.v:
	cat2coq7 -nocat -defined MFENCE -defs ra x86tso.cat -overwrite
tso_nosm.v:
	cat2coq7 -nocat -defined MFENCE -defs ra tso_nosm.cat -overwrite
rc11.v:
	cat2coq7 -nocat -defs ra rc11.cat -overwrite
## remove this to deal with the real sc.cat
# sc.v:
# 	cat2coq7 -nocat -defs ra sc.cat -overwrite

zoo.vo: x86tso.vo tso_nosm.vo sc_nosm.vo rc11.vo

%.v: %.cat
	cat2coq7 -nocat -defs ra $< -overwrite

%.vo: %.v
	coqc $<

clean:
	rm -f *.vo *.vok *.vos *.glob Cat.v sc.v x86tso.v sc_nosm.v rc11.v tso_nosm.v
