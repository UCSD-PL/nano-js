/*@ include singly-linked-list.js */

/*@
  remove ::
    (x:<l>+null, k:number)/l |-> xs:list[number]
     => {v:<m>+null | (keysp(v,ms) = Set_dif(keysp(x,xs),Set_sng(k)))}
        /m |-> ms:list[number]
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
  }

  return null;
}
