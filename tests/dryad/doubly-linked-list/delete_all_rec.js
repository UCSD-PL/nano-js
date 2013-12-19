/*@ include doubly-linked-list.js */

/*@ qualif LLen(v:a, y:c, ys:d):
      (keys(v) = (Set_cup(Set_sng(field(y, "data")),
                          dkeysp(field(y, "next"), ys)))) */

/*@ remove :: forall A P.
  (x:<l>+null,k:A)/l |-> ls:dlist[A,<l>,P]
    => r:{v:<v>+null | dkeysp(v,vs) = Set_dif(dkeysp(x,ls),Set_sng(k))}
       /v |-> vs:dlist[A,<v>,null] */
function remove(x, k){
  if (x == null){
    return null;
  } else {
    var d = x.data;
    var r = remove(x.next,k);
    x.prev = null;
    x.next = r;
    
    if (d != k) {
      if (r != null) {
        r.prev = x;
      }
      return x;
    } else {
      delete(x);
      if (r != null) {
        r.prev = null;
      } 
      return r;
    }
  }
}
