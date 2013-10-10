//import "doubly-linked-list.js";

// fix this modulo nulls

/*@ type dlist[A,S,P] exists! l |-> dlist[A, <l>, S] . { data: A, next:<l>+null, prev:P } */

/* delete_at_middle ::  
      (u:?rdlist[A,<l>], p:<l>, v:?dlist[A,<l>])/h
      => void/ u |-> {rdlist[A,v] | keys(u) = keys(u,h)} * v |-> { dlist[A,<u>] | keys(v) = keys(v,h)} 
 */

/*@ delete_at_middle :: forall A P R.
      (p:<p>+null, q:<q>, r:<r>+null)/p |-> dlist[A,<p>,P] * q |-> dlist[A,<q>,<p>+null] * r |-> dlist[A,<r>,R]
      => void/p |-> dlist[A,<p>,P] * r |-> dlist[A,<r>,<p>+null]
 */
function delete_at_middle (p, q, r){

  if (typeof(p) != "null") {
    p.next = r;
  }

  if (typeof(r) != "null") {
    r.prev = p;
  }

  return;
}
