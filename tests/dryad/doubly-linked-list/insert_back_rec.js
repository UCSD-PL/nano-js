//import "singly-linked-list.js"

/*@
  type dlist[A,S,P] exists! l |-> ls:dlist[A, <l>, S] . me:{ data: A, next:<l>+null, prev:P }

  with len(x) := (if (ttag(field(me,"next")) = "null") then 1 else (1 + len(ls)))
*/

/* insert :: (x:?dlist[A,null], k:A)/h => {v:dlist[A,null]}/ v |-> keys(v) = set_cup(keys(x,h), set_singleton(k)) */

/*@

  insert :: forall A P. (x:<l>+null, k:A)/l |-> ls:dlist[A,<l>,P]
                                   => <k>/k |-> ks:{dlist[A,<k>,null] | (if (ttag(x) = "null") then
                                                                           (len(v) = 1)
                                                                        else
                                                                           (len(v) = (len(ls) + 1))) }
*/
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

