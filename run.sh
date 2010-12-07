EXT="byte"
TARGETS="iteratees.$EXT tests_direct.$EXT"
# bash
rm -f $TARGETS && ocamlbuild iteratees.inferred.mli $TARGETS && \
  (for X in $TARGETS;
   do
     echo "--------- $X: ---------"
     ./$X
   done
   echo "------------------"
  )
