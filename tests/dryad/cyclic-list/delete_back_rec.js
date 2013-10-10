import "cyclic_lists.js";

/*@ remove :: (p:clist[A,<q>], {q:clist[A,<q>] | q != p}) 
           => ?<r>/r |-> {clist[A,<q>] | len(r) = len(p,h) - 1} 
 */

function remove(p, q){
  if (p.next == q) {
    return null;
  } else {
    var t  = remove(p.next, q);
    p.next = t ? t : q;
    return p;
  }
}


<l0> -> <l1> -----> <l0>
