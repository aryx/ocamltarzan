OCAMLC=ocamlc -c -pp "camlp4orf " -I +camlp4 -unsafe-string
OCAMLDEP=ocamldep -pp "camlp4orf " -I +camlp4

##############################################################################
# Variables
##############################################################################
# called fakelib because we are not interested really in the .cma, but
# in the different .cmo this directory build, .cmo that can be used
# by ocamltarzan after.
TARGET=fakelib

SRC= pa_type_conv.ml \
     pa_xxx_of.ml \
     pa_sexp_conv.ml pa_bin_prot.ml \
     type.ml pa_type.ml \
     pa_value.ml \
     pa_rpc.ml \
     pa_sof.ml pa_ofs.ml \
     pa_visitor.ml pa_map.ml pa_map_todo.ml pa_iter_env.ml \
     pa_vof.ml pa_ofv.ml  pa_tof.ml \
     pa_matcher.ml \
     pa_json_of.ml

#inlined in pa_value.ml: p4_value.ml
#inlined in pa_type.ml:  p4_type.ml

OBJS?=    $(SRC:.ml=.cmo)

all: $(TARGET).cma
all.opt: 

$(TARGET).cma: $(OBJS) $(LIBS)
	ocamlc -a -o $@ $(OBJS)


.SUFFIXES:
.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(OCAMLC)  -c $<
.mli.cmi:
	$(OCAMLC)  -c $<


#	ocamlc -c -I +camlp4 pa_type_conv.mli
#	ocamlc -c -pp "camlp4orf " -I +camlp4 pa_type_conv.ml
#	echo
#	ocamlc -c -I +camlp4 pa_sexp_conv.mli
#	ocamlc -c -pp "camlp4orf " -I +camlp4 pa_sexp_conv.ml
#	echo
#	ocamlc -c -I +camlp4 pa_bin_prot.mli
#	ocamlc -c -pp "camlp4orf " -I +camlp4 pa_bin_prot.ml

clean::
	rm -f *.cm[iox] *.o *.a *.cma *.cmxa *.annot


opt:

depend:

clean::

distclean:
	rm -f .depend

depend: 
	$(OCAMLDEP) *.mli *.ml  > .depend

-include .depend
