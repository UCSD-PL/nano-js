/*@ include doubly-linked-list.js */

/*@
  insert :: forall P.
    (x:<x>+null, k:number)/x |-> xs:dlist[number,<x>,P]
       => r:<j>/j |-> js:{v:dlist[number,<j>,null] | (((len v) = 1 + (len xs))
                                                  && ((keys v) = (Set_cup (Set_sng k) (keys xs))))}
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

