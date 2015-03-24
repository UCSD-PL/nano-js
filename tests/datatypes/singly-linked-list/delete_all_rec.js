/*@ include singly-linked-list.js */

/*@
  remove ::
    (x:<l>+null, k:number)/l |-> xs:list[number] => 
    <m>+null/m |-> ms:{v:list[number] | (keys(v) = Set_dif(keys(xs),Set_sng(k)))}
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
