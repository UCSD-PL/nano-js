
/*@ remove :: (x:dlist[A, null], k:A)/h => {v:dlist[A, null]}/v |-> keys(v) = set_minus(keys(x,h), set_singleton(k)) */

function remove(x, k){
  if (!x){
    return x;
  } else {
    var t = remove(x.next, k);
    if (x.data == k) {
      return t;
    } else {
      x.next = t;
      t.prev = x;
      return x;
    }
  } 
}
