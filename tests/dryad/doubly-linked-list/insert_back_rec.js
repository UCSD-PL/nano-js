import "singly-linked-list.js"

/*@ insert :: (x:?dlist[A,null], k:A)/h => {v:dlist[A,null]}/ v |-> keys(v) = set_cup(keys(x,h), set_singleton(k)) */

function insert(x, k){
  if (x){
    var y  = x.next;
    var t  = insert(y, k);
    x.next = t;
    t.prev = x;
    return x;
  } else {
    var y  = {}; // {data : k, next : null, prev: null};
    y.data = k;
    y.next = null;
    y.prev = null;
    return y;
  }
}

