PKG=iteratees
VERSION=0.1

TESTBIN=tests_lwt.byte

all :
	ocamlbuild \
	   iteratees.cma iteratees.cmxa tests_lwt.byte tests_lwt.native \
	   tests_direct.byte tests_direct.native

install : all
	ocamlfind install \
	  -patch-version $(VERSION) \
	  $(PKG) META \
	  _build/iteratees.cma _build/iteratees.cmxa _build/iteratees.a \
	  _build/iteratees.cmi \
	  _build/it_Lwt_IO.cmi _build/direct_IO.cmi \
	  _build/iteratees_http.cmi \
	  _build/it_misc.cmi _build/it_Ops.cmi _build/it_Types.cmi \
	  _build/subarray_cat.cmi _build/subarray.cmi

deinstall :
	ocamlfind remove $(PKG)

uninstall :
	$(MAKE) deinstall

reinstall :
	-$(MAKE) deinstall
	$(MAKE) install

tests : all
	_build/$(TESTBIN)
