//import "doubly-linked-list.js"

/*@ type dlist[A,S,P] exists! l |-> dlist[A, <l>, S] . { data: A, next:<l>+null, prev:P } */

/* insert :: (x:?dlist[A,null], k:A)/h => {v:dlist[A,null]}/v |-> keys(v) = set_cup(keys(x,h), set_singleton(k))} */

/*@ insert :: forall A. (x:<x>+{null | true}, k:A)/x |-> dlist[A,<x>,null] => <v>/v |-> dlist[A,<v>,{null | true}] */
function insert(x, k){
  var y  = {};
  y.data = k;
  y.next = x;
  y.prev = null;

  if (typeof(x) != "null") {
      x.prev = y;
  }

  return y;
}

