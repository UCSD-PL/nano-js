import "singly-linked-list.js"

/*@ remove :: (x:list[A], k:A)/h => {v:list[A]| keys(v) = set_minus(keys(x,h), set_singleton(k))} */

// OR 

/*@ remove :: (x:list[A], k:A)/h => {v:list[A]}/v |-> keys(v) = set_minus(keys(x,h), set_singleton(k)) */

function remove(x, k){
  if (!x){
    return x;
  } else {
    var t = remove(x.next, k);
    if (x.data == k) {
      return t;
    } else {
      x.next = t;
      return x;
    }
  } 
}
