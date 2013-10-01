import "singly-linked-list.js"


/*@ insert :: (x:?list[A], k:A) => {v:list[A]| keys(v) = set_cup(keys(x), set_singleton(k))} */
function insert(x, k){
  if (x){
    var y  = {};
    y.data = k;
    y.next = x;
    return y;
  } else {
    var y  = {};
    y.data = k;
    y.next = null;
    return y;
  }
}
