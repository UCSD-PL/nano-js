/*@ include doubly-linked-list.js */

/*@ remove :: forall P.
  (x:<l>+null,k:number)/l |-> ls:dlist[number,<l>,P]
    => <v>+null
       /v |-> vs:{v:dlist[number,<v>,null] | (keys v) = (Set_dif (keys ls) (Set_sng k))} */
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
        return x;
      } else {
        return x;
      }
    } else {
      delete(x);
      if (r != null) {
        r.prev = null;
        return r;
      } else {
        return r;
      }
    }
  }
}
