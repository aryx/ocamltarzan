
MAKESUBDIRS=lib-sexp pa

all:
	$(MAKE) rec 
	$(MAKE) ocamltarzan
opt: 
	$(MAKE) rec.opt

INCLUDES=-I external/commons
LIBS=external/commons/commons.cma
SYSLIBS=unix.cma str.cma

ocamltarzan: ocamltarzan.ml 
	ocamlc -o $@ -custom $(INCLUDES) $(SYSLIBS) $(LIBS)  ocamltarzan.ml 
clean::
	rm -f ocamltarzan

rec:
	set -e; for i in $(MAKESUBDIRS); do $(MAKE) -C $$i all; done 
rec.opt:
	set -e; for i in $(MAKESUBDIRS); do $(MAKE) -C $$i all.opt; done 

clean::
	rm -f *.cm[iox] *.o *.a *.cma *.cmxa *.annot

clean::
	set -e; for i in $(MAKESUBDIRS); do $(MAKE) -C $$i clean; done 
depend::
	set -e; for i in $(MAKESUBDIRS); do $(MAKE) -C $$i depend; done
distclean::
	set -e; for i in $(MAKESUBDIRS); do $(MAKE) -C $$i distclean; done 

test:
	echo "testing tof"
	./ocamltarzan -choice tof tests/expr.ml
	echo "testing vof"
	./ocamltarzan -choice vof tests/expr.ml
