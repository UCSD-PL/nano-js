/*@ include doubly-linked-list.js */

// In below, separation between x and v in output IS obvious.
/*@ qualif LLen(v:a): ((ttag(x1) != "null") => (if (ttag(x2) = "null") then (len(v) = len(ls)) else (len(v) = len(ls) + len(ms)))) */

/*@ append :: forall A P.
  (x1:<l>+null, x2:<m>+null)/l |-> x1s:dlist[A,<l>,P] * m |-> x2s:dlist[A,<m>,null]
      => {v:<k>+null | true }
        /k |-> ks:dlist[A,<k>,null]
*/
function append(x1, x2) {
    if (x1 != null) {
        var n = x1.next;
        var t = append(n, x2);

        x1.next = t;
        x1.prev = null;

        if (t != null) {
            t.prev = x1;
        } 

        return x1;
    } else {
        return x2;
    }
}

