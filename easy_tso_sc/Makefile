all: eq.vo sc.v tso.v

tso.vo sc.vo: Cat.vo
eq.vo: tso.vo sc.vo Cat.vo

opt="-notations none -defs ra"

Cat.v:
	cat2coq7 -notations none -defs ra -yescat -overwrite

%.v: %.cat
	cat2coq7 -notations none -defs ra $< -overwrite

%.vo: %.v
	coqc $<


clean:
	rm -f *.vo *.vok *.vos *.glob Cat.v sc.v tso.v
