//import "singly-linked-list.js"

// In below, separation between x and v in output IS obvious.

/*@ type dlist[A,S,P] exists! l |-> dlist[A, <l>, S] . { data: A, next:<l>+null, prev:P } */

/* append::(x1:dlist[A,null], x2:dlist[A,null])/h 
               => {v:dlist[A,null]}/ v |-> keys(v) = set_cup(keys(x1,h), keys(x2,h)) */

/* append :: forall A.
  (x1:<l>+null, <m>+null)/ l |-> dlist[A,<l>,null] * m |-> dlist[A,<m>,null]
    => <k>+null/k |->dlist[A,<k>,{null | true}] */

/*@ append :: forall A.
  (x1:<l>, <m>)/ l |-> dlist[A,<l>,null] * m |-> dlist[A,<m>,null]
    => <k>+null/k |->dlist[A,<k>,{null | true}] */
function append(x1, x2) {
  // if (typeof(x1) == "null")
  // {
  //   // return x2;
  //     return null;
  // }
  // else
  // {
    var z   = x1.next;
    // var t   = append(z, x2);
    // x1.next = t;
    return x1;
    // x1.next = t;
    // t.prev  = x1;
    // return x1;
  // } 
}

