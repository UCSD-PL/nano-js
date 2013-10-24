//import "singly-linked-list.js"

/* remove :: (x:list[A], k:A)/h => {v:list[A]| keys(v) = set_minus(keys(x,h), set_singleton(k))} */

// OR 

/* remove :: (x:list[A], k:A)/h => {v:list[A]}/v |-> keys(v) = set_minus(keys(x,h), set_singleton(k)) */

/*@ remove :: forall A. (x:<l>+{null | true}, k:A)/l |-> list[A] => <m>+null/m |-> list[A] */
function remove(x, k){
  if (typeof(x) != "null") {
    var xn = x.next;
    x.next = remove(xn, k);
    if (x.data == k) {
      var n = x.next;
      return n;
    } else {
      return x;
    }
  } else {
    return null;
  } 
}
