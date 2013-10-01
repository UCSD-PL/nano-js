import "singly-linked-list.js"

/*@ insert :: (x:?list[A], k:A) => {v:list[A]| keys(v) = set_cup(keys(x), set_singleton(k))} */
function insert(x, k){
  if (x){
    var y  = x.next;
    var t  = insert(y, k);
    x.next = t;
    return x;
  } else {
    var y  = {}; // {data : k, next : null };
    y.data = k;
    y.next = null;
    return y;
  }
}
