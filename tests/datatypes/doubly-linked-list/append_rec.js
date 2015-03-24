/*@ include doubly-linked-list.js */

/*@ append :: forall P.
  (x1:<r>+null, x2:<m>+null)/r |-> x1s:dlist[number,<r>,P] * m |-> x2s:dlist[number,<m>,null]
      => {v:<k>+null | ((v = null) <=> (x1 = null && x2 = null))}
         /k |-> ks:{v:dlist[number,<k>,null] | ((len v) = (len x1s) + (len x2s) 
                                            && (keys v) = (Set_cup (keys x1s) (keys x2s))) }
*/
function append(x1, x2) {
  if (x1 == null)
    return x2;

  x1.prev = null;
  
  if (x2 == null)
    return x1;

  var n = x1.next;
  var t = append(n, x2);

  x1.next = t;
  x1.prev = null;
  t.prev = x1;

  return x1;
}
