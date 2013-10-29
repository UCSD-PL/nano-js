//import "singly-linked-list.js"

// In below, separation between x and v in output IS obvious.
/*@ qualif LLen(v:a): ((ttag(x1) != "null") => (if (ttag(x2) = "null") then (len(v) = len(ls)) else (len(v) = len(ls) + len(ms)))) */

/*@
  type dlist[A,S,P] exists! l |-> ls:dlist[A, <l>, S] . me:{ data: A, next:<l>+null, prev:P }

  with len(x) := (if (ttag(field(me,"next")) = "null") then 1 else (1 + len(ls)))
*/

/* append::(x1:dlist[A,null], x2:dlist[A,null])/h 
               => {v:dlist[A,null]}/ v |-> keys(v) = set_cup(keys(x1,h), keys(x2,h)) */

/*@ append :: forall A P.
  (x1:<l>+null, x2:<m>+null)/l |-> ls:dlist[A,<l>,P] * m |-> ms:dlist[A,<m>,null]
      => {v:<k>+null | (((ttag(x1) = "null") && (ttag(x2) = "null")) <=> (ttag(v) = "null"))}
        /k |-> ks:{dlist[A,<k>,null] | (if (ttag(x1) = "null")
                                            then (if (ttag(x2) = "null")
                                                     then true
                                                     else (len(v) = len(ms)))
                                            else (if (ttag(x2) = "null")
                                                     then (len(v) = len(ls))
                                                     else (len(v) = len(ls) + len(ms)))) } 
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

