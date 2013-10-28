//import "doubly-linked-list.js"
/*@ qualif NNull0(v:a, x:b): ((ttag(x)  = "null") => (ttag(v) = "null")) */
/*@ qualif NNull0(v:a, x:b): ((ttag(x) != "null") => (x = v)) */
/*@ qualif EqLen(v:a, x:b): (len(v) = len(x)) */

/*@
  type dlist[A,S,P] exists! l |-> ls:dlist[A, <l>, S] . me:{ data: A, next:<l>+null, prev:P }

  with len(x) := (if (ttag(field(me,"next")) = "null") then 1 else (1 + len(ls)))
*/

/* insert :: (x:?dlist[A,null], k:A)/h => {v:dlist[A,null]}/v |-> keys(v) = set_cup(keys(x,h), set_singleton(k))} */

/*@ insert :: forall A. (x:<x>+null, k:A)/x |-> xs:dlist[A,<x>,null]
                                   => <v>/v |-> ys:{dlist[A,<v>,null] | (if (ttag(x) != "null")
                                                                        then (len(v) = 1 + len(xs))
                                                                        else (len(v) = 1)) } */
function insert(x, k){
  var y  = {data:k, next:null, prev:null};

  if (typeof(x) != "null") {
      x.prev = y;
      y.next = x;
  }

  return y;
}

