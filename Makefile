MAKESUBDIRS=lib-sexp pa

#pa
#TARGET=ocamltarzan

all:
	$(MAKE) rec 
	$(MAKE) ocamltarzan

opt: 
	$(MAKE) rec.opt
all.opt: opt


ocamltarzan: ocamltarzan.ml common.ml
	ocamlc -o $@ unix.cma str.cma common.ml ocamltarzan.ml 
#	ocamlc -o $@ -I ../commons unix.cma str.cma ../commons/commons.cma ocamltarzan.ml 
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

