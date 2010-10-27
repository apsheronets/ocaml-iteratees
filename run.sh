TARGETS="iteratees.byte tests.byte"
# bash
rm -f $TARGETS && ocamlbuild iteratees.inferred.mli $TARGETS && \
  (for X in $TARGETS;
   do
     echo "--------- $X: ---------"
     ./$X
   done
   echo "------------------"
  )
