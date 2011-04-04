EXT="byte"
TARGETS="iteratees.$EXT tests_direct.$EXT"
# bash

# ocamlbuild iteratees.inferred.mli && \
#   grep -A 5 "val limit" _build/iteratees.inferred.mli
# exit

rm -f $TARGETS && ocamlbuild iteratees.inferred.mli $TARGETS && \
  (for X in $TARGETS;
   do
     echo "--------- $X: ---------"
     ./$X
   done
   echo "------------------"
  )
