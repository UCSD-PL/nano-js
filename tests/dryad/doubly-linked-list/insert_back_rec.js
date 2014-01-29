/*@ include doubly-linked-list.js */

/*@
  insert :: forall P.
    (x:<l>+null, k:number)/l |-> xs:dlist[number,<l>,P]
       => r:{v:<k> | ((dlenp(v,ks) = 1+dlenp(x,xs))
                   && (dkeysp(v,ks) = dkeysp(x,xs) ∪1 k)) }
         /k |-> ks:dlist[number,<k>,null]
*/
function insert(x, k){
  if (x != null){
    var y  = x.next;
    var t  = insert(y, k);
    x.next = t;
    t.prev = x;
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

