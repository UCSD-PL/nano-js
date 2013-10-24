//import "singly-linked-list.js"

// In below, separation between x and v in output IS obvious.

/*@ type dlist[A,S,P] exists! l |-> dlist[A, <l>, S] . { data: A, next:<l>+null, prev:P } */

/* append::(x1:dlist[A,null], x2:dlist[A,null])/h 
               => {v:dlist[A,null]}/ v |-> keys(v) = set_cup(keys(x1,h), keys(x2,h)) */

/*@ append :: forall A P.
  (x1:<l>+null, x2:<m>+null)/l |-> ls:dlist[A,<l>,P] * m |-> ms:dlist[A,<m>,null] => <k>+null/k |-> ks:dlist[A,<k>,{null | true}]
*/
function append(x1, x2) {
    if (typeof(x1) != "null") {
        var n = x1.next;
        var t = append(n, x2);

        x1.next = t;
        x1.prev = null;

        if (typeof(t) != "null") {
            t.prev = x1;
        }

        return x1;
    } else {
        return x2;
    }
}

