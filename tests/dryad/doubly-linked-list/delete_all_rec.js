
/*@ type dlist[A,S,P] exists! l |-> dlist[A, <l>, S] . { data: A, next:<l>+null, prev:P } */
/* remove :: (x:dlist[A, null], k:A)/h => {v:dlist[A, null]}/v |-> keys(v) = set_minus(keys(x,h), set_singleton(k)) */

/*@ remove :: forall A P.
  (x:<l>+null,k:A)/ l |-> dlist[A,<l>,P] => <v>+null/v |-> dlist[A,<v>,P] */
function remove(x, k){
  if (typeof(x) == "null"){
    return x;
  } else {
    var d = x.data;
    var n = x.next;

    if (d == k) {
        return remove(n,k);
    } else {
        var t = remove(n,k);
        x.next = t;
        t.prev = x;
        return x;
    } 
  }
}
