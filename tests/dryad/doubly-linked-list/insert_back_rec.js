/*@ include doubly-linked-list.js */

/*@
  insert :: forall A P.
    (x:<l>+null, k:A)/l |-> xs:dlist[A,<l>,P]
       => r:{v:<k> | ((dlenp(v,ks) = 1+dlenp(x,xs))
                   && (dkeysp(v,ks) = Set_cup(Set_sng(k),dkeysp(x,xs)))) }
         /k |-> ks:dlist[A,<k>,null]
*/
function insert(x, k){
  if (x != null){
    var y  = x.next;
    var t  = insert(y, k);
    t.prev = x;
    x.next = t;
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

