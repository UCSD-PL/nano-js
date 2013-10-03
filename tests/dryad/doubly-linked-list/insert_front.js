import "doubly-linked-list.js"

/*@ insert :: (x:?dlist[A,null], k:A)/h => {v:dlist[A,null]}/v |-> keys(v) = set_cup(keys(x,h), set_singleton(k))} */
function insert(x, k){
  var y  = {};
  y.prev = null;
  y.data = k;
  y.next = x;
  if (x) { x.prev = y; }
  return y;
}

