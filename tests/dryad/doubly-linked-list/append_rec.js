import "singly-linked-list.js"

// In below, separation between x and v in output IS obvious.

/*@ append::(x1:dlist[A,null], x2:dlist[A,null])/h 
               => {v:dlist[A,null]}/ v |-> keys(v) = set_cup(keys(x1,h), keys(x2,h)) */

function append(x1, x2){
  if (!x1){
    return x2;
  } else {
    var z   = x1.next;
    var t   = append(z, x2);
    x1.next = t;
    t.prev  = x1;
    return x1;
  } 
}

