/*@ include doubly-linked-list.js */
/*@ qualif EqMeas(v:a, vs:b): ((dlenp(v,vs) = dlenp(x,xs))
                              && (dkeysp(v,vs) = dkeysp(x,xs))) */
/*@
  insert ::
    (x:<x>+null, k:number)/x |-> xs:dlist[number,<x>,null]
       => r:{v:<j> | ((dlenp(v,js) = 1 + dlenp(x,xs))
                  && (dkeysp(v,js) = dkeysp(x,xs) ∪1 k))}
         /j |-> js:dlist[number,<j>,null]
*/
function insert(x, k){
  var y  = {data:k, next:x, prev:null};

  if (x != null) {
    x.prev = y;
  }

  return y;
}

