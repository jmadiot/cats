# models=sc_nosm tso_nosm x86tso

all: zoo.vo tso_nosm.v x86tso.v sc_nosm.v rc11.v

x86tso.v:
	cat2coq7 -defined MFENCE -defs ra x86tso.cat -overwrite
tso_nosm.v:
	cat2coq7 -defined MFENCE -defs ra tso_nosm.cat -overwrite
rc11.v:
	cat2coq7 -defs ra rc11.cat -overwrite
## remove this to deal with the real sc.cat
# sc.v:
# 	cat2coq7 -defs ra sc.cat -overwrite

x86tso.vo sc.vo: Cat.vo
zoo.vo: x86tso.vo tso_nosm.vo sc_nosm.vo Cat.vo rc11.vo

Cat.v:
	cat2coq7 -defs ra -yescat -overwrite

%.v: %.cat
	cat2coq7 -defs ra $< -overwrite

%.vo: %.v
	coqc $<

clean:
	rm -f *.vo *.vok *.vos *.glob Cat.v sc.v x86tso.v sc_nosm.v rc11.v tso_nosm.v
