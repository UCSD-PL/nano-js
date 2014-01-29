/*@ include doubly-linked-list.js */

/*@ qualif LLen(v:a, y:c, ys:d):
    ((len(v)  = 1 + dlenp(field(y, "next"), ys))
  && (keys(v) = Set_cup(Set_sng(field(y, "data")),
                        dkeysp(field(y, "next"), ys)))) */

/*@ append :: forall P.
  (x1:<r>+null, x2:<m>+null)/r |-> x1s:dlist[number,<r>,P]
                           * m |-> x2s:dlist[number,<m>,null]
      => {v:<k>+null | ((dlenp(v,ks) = dlenp(x1,x1s) + dlenp(x2,x2s)) 
                     && (dkeysp(v,ks)= Set_cup(dkeysp(x1,x1s),dkeysp(x2,x2s))))}
        /k |-> ks:dlist[number,<k>,null]
*/
function append(x1, x2) {
  if (x1 == null) {
    return x2;
  }
  var n = x1.next;
  var t = append(n, x2);

  x1.next = t;
  x1.prev = null;

  if (t != null) {
    t.prev = x1;
  }

  return x1;
}

