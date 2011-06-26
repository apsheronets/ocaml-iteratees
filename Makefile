PKG=iteratees
VERSION=0.4

TESTBIN=tests_lwt.byte
#TESTBIN=tests_pure.byte

all :
	ocamlbuild \
	   iteratees.cma iteratees.cmxa tests_lwt.byte tests_lwt.native \
	   tests_direct.byte tests_direct.native \
	   tests_pure.byte tests_pure.native \
	   get_sig.byte
	-_build/get_sig.byte > _build/it_type.ml
	# (cd _build && ocamlc -c -pp camlp4r it_type.ml)

install : all
	ocamlfind install \
	  -patch-version $(VERSION) \
	  $(PKG) META \
	  _build/iteratees.cma _build/iteratees.cmxa _build/iteratees.a \
	  _build/iteratees.cmi \
	  _build/it_Lwt_IO.cmi _build/direct_IO.cmi \
	  _build/iteratees_http.cmi \
	  _build/it_misc.cmi _build/it_Ops.cmi _build/it_Types.cmi \
	  _build/subarray_cat.cmi _build/subarray.cmi _build/pure_IO.cmi \
	  -optional _build/it_type.ml

deinstall :
	ocamlfind remove $(PKG)

uninstall :
	$(MAKE) deinstall

reinstall :
	-$(MAKE) deinstall
	$(MAKE) install

tests : all
	_build/$(TESTBIN)
