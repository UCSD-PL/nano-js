/*@ include singly-linked-list.js */

/*@ insert :: 
  (x:<l>+null, k:number)/l |-> xs:list[number]
    => r:{v:<m> | ((lenp(v,ys) = 1 + lenp(x,xs))
                && (keysp(v,ys) = keysp(x,xs) ∪1 k)) }
      /m |-> ys:list[number]
*/
function insert(x, k){
  if (x != null){
    var n = x.next;
    var t = insert(n, k);
    x.next = t;
    return x;
  }
  var y  = {data:k, next:null};
  return y;
}