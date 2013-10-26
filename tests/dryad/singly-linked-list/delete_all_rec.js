//import "singly-linked-list.js"

/* remove :: (x:list[A], k:A)/h => {v:list[A]| keys(v) = set_minus(keys(x,h), set_singleton(k))} */

// OR 

/* remove :: (x:list[A], k:A)/h => {v:list[A]}/v |-> keys(v) = set_minus(keys(x,h), set_singleton(k)) */

/*@ remove :: forall A. (x:<l>+{null | true}, k:A)/l |-> ls:list[A]
                          => <m>+null/m |-> ms:list[A]*/
function remove(x, k){
  if (typeof(x) != "null") {
    var xn = x.next;
    var t = remove(xn, k);
    x.next = t;
    var d = x.data;
    if (d == k) {
      var n = x.next;
      return n;
    } else {
      return x;
    }
  } else {
    return null;
  } 
}
