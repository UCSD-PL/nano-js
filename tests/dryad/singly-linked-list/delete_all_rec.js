//import "singly-linked-list.js"

/*@
  remove :: forall A.
    (x:<l>+null, k:A)/l |-> xs:list[A]
     => {v:<m>+null | (keysp(v,ms) = Set_dif(keysp(x,xs),Set_sng(k)))}
        /m |-> ms:list[A]
*/
function remove(x, k){
  if (x != null) {
    var xn = x.next;
    var t = remove(xn, k);
    x.next = t;
    var d = x.data;
    if (d == k) {
      return t;
    } else {
      return x;
    }
  } else {
    r = null;
    return r;
  } 
}
