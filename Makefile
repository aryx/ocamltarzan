
MAKESUBDIRS=lib-sexp pa

INCLUDES=-I external/commons
# commons.cma now depends on multiple libs :(
LIBS=external/calendar/calendarLib.cma external/easy-format/easy_format.cma \
  external/ppx_deriving/runtime/ppx_deriving_runtime.cma external/ppx_deriving_yojson/runtime/ppx_deriving_yojson_runtime.cma \
  external/biniou/biniou.cma external/yojson/yojson.cma \
  external/easy_logging/easy_logging.cma external/easy_logging_yojson/easy_logging_yojson.cma \
  external/commons/commons.cma
SYSLIBS=unix.cma str.cma

all:
	$(MAKE) rec 
	$(MAKE) ocamltarzan
opt: 
	$(MAKE) rec.opt

# -unsafe-string not anymore available in 4.12
ocamltarzan: ocamltarzan.ml 
	ocamlc -o $@ -unsafe-string -custom $(INCLUDES) $(SYSLIBS) $(LIBS)  ocamltarzan.ml 
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
