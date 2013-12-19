/*@ include doubly-linked-list.js */
/*@ qualif EqMeas(v:a, vs:b): ((dlenp(v,vs) = dlenp(x,xs))
                              && (dkeysp(v,vs) = dkeysp(x,xs))) */
/*@
  insert :: forall A.
    (x:<x>+null, k:A)/x |-> xs:dlist[A,<x>,null]
       => r:{v:<j> | ((dlenp(v,js) = 1 + dlenp(x,xs))
                  && (dkeysp(v,js) = Set_cup(Set_sng(k), dkeysp(x,xs))))}
         /j |-> js:dlist[A,<j>,null]
*/
function insert(x, k){
  var y  = {data:k, next:x, prev:null};

  if (x != null) {
    y.next = x;
    x.prev = y;
  }

  return y;
}

