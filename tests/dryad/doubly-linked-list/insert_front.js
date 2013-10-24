//import "doubly-linked-list.js"
/*@ qualif EqNull(v:a, x:b): (((ttag v) = "null") => ((ttag x) = "null")) */

/*@ type dlist[A,S,P] exists! l |-> dlist[A, <l>, S] . { data: A, next:<l>+null, prev:P } */

/* insert :: (x:?dlist[A,null], k:A)/h => {v:dlist[A,null]}/v |-> keys(v) = set_cup(keys(x,h), set_singleton(k))} */

/*@ insert :: forall A. (x:<x>+{null | true}, k:A)/x |-> xs:dlist[A,<x>,null] => <v>/v |-> ys:dlist[A,<v>,{null | true}] */
function insert(x, k){
  var y  = {};
  y.data = k;
  y.next = null;
  y.prev = null;

  if (typeof(x) != "null") {
      x.prev = y;
      y.next = x;
  }

  return y;
}

