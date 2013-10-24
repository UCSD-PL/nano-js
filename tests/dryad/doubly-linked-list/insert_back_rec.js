//import "singly-linked-list.js"

/*@ type dlist[A,S,P] exists! l |-> dlist[A, <l>, S] . { data: A, next:<l>+null, prev:P } */

/* insert :: (x:?dlist[A,null], k:A)/h => {v:dlist[A,null]}/ v |-> keys(v) = set_cup(keys(x,h), set_singleton(k)) */

/*@ insert :: forall A P. (x:<l>+null, k:{A | true})/l |-> ls:dlist[A,<l>,P] => <k>/k |-> ks:dlist[A,<k>,null] */
function insert(x, k){
  if (typeof(x) != "null"){
    var y  = x.next;
    var t  = insert(y, k);
    t.prev = x;
    x.next = t
    x.prev = null;
    return x;
  } else {
    var y  = {}; // {data : k, next : null, prev: null};
    y.data = k;
    y.next = null;
    y.prev = null;
    return y;
  }
}

