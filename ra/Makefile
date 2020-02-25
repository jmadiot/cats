
cat_vs=LL.v aarch64_obsolete.v aarch64.v aarch64fences.v arm_alt.v arm.v armfences.v armllh.v atom_arm.v atom.v c11_base.v c11_cos.v c11_los.v c11_orig.v c11_partialSC.v c11_simp.v compat.v cos.v coscat.v cross.v doc64.v fences.v filters.v fulleieio.v herd.v herdcat.v lessrelaxed.v mini.v minimal.v minimalcat.v mips_tso.v mips.v mipsfences.v naked.v ppc_checks.v ppc.v ppcfences.v ppo.v pretty.v prettycat.v qualcomm.v rc11.v riscv_defs.v riscv_total.v riscv.v sc.v sc2.v sccat.v simple_arm.v simple_c11.v stdlib.v tso.v uni.v uniproc_sca.v uniproc_normw_cat.v uniproc.v uniproccat.v x86fences.v x86tso.v

cat_vos=$(cat_vs:=o)

all_vos=$(cat_vos) Cat.vo importeverything.vo

all: $(all_vos)
importeverything.vo: $(cat_vos)
$(cat_vos): Cat.vo

%.vo: %.v
	coqc $<
clean:
	rm -f $(all_vos) $(all_vos:vo=glob) $(all_vos:vo=vok) $(all_vos:vo=vos) $(addprefix .,$(all_vos:vo=aux))
