/*@ include singly-linked-list.js */

/*@ insert ::
  (x:{v:<l>+null | (Prop(nil(v)) => Prop(nil(xs)))}, k:number)/l |-> xs:list[number] =>
                    <m>/m |-> ys:{v:list[number] | len(v) = len(xs) + 1} */
function insert(x, k) {
  var y = {data:k, next:x};
  return y;
}
