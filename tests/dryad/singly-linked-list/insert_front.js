/*@ include singly-linked-list.js */

/*@ insert :: forall A.
  (x:<l>+null, k:A)/l |-> xs:list[A] =>
                   {v:<m> | ((lenp(v,ys) = lenp(x,xs) + 1)
                          && (keysp(v,ys) = Set_cup(Set_sng(k),keysp(x,xs)))) }
                             /m |-> ys:list[A] */
function insert(x, k) {
  var y = {};
  y.data = k;
  y.next = x;
  return y;
}
