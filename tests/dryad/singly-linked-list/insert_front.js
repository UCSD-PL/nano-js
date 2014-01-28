/*@ include singly-linked-list.js */

/*@ insert ::
  (x:<l>+null, k:number)/l |-> xs:list[number] =>
                   {v:<m> | ((lenp(v,ys) = lenp(x,xs) + 1)
                          && (keysp(v,ys) = keysp(x,xs) ∪1 k)) }
                   /m |-> ys:list[number] */
function insert(x, k) {
  var y = {};
  y.data = k;
  y.next = x;
  return y;
}
