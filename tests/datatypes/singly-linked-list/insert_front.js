/*@ include singly-linked-list.js */

/*@ insert ::
  (x:<l>+null, k:number)/l |-> xs:list[number] => <m>/m |-> ys:{v:list[number] | ((keys(v) = Set_cup(Set_sng(k),keys(xs))) && (len(v) = len(xs) + 1))} */
function insert(x, k) {
  var y = {data:k, next:x};
  return y;
}
