//import "doubly-linked-list.js";

// fix this modulo nulls

/*@ type dlist[A,S,P] exists! l |-> dlist[A, <l>, S] . { data: A, next:<l>+null, prev:P } */

/* delete_at_middle ::  
      (u:?rdlist[A,<l>], p:<l>, v:?dlist[A,<l>])/h
      => void/ u |-> {rdlist[A,v] | keys(u) = keys(u,h)} * v |-> { dlist[A,<u>] | keys(v) = keys(v,h)} 
 */

/*@ delete_at_middle :: forall A.
      (p:<p>+null, q:<q>, r:<r>+null)/p |-> pp:{ data:A, next:{v:<q> | v = q} + null, prev:null }
                                    * q |-> qq:{ data:A, next:{v:<r> | v = r} + {v:null | v = r}, prev:{v:<p> | v = p} + {v:null | v = p} }
                                    * r |-> rr:dlist[A,<r>,{v:<q> | v = q}+null]
      => void/p |-> p:{ data:A, next:<r>+null, prev:null} * r |-> r:dlist[A,<r>,{v:<p> | v = p }+{v:null | v = p}] 
 */
function delete_at_middle (p, q, r){
  q.next = null;
  q.prev = null;

  delete(q);  

  if (typeof(p) != "null") {
      p.next = r;
  }

  if (typeof(r) != "null") {
      r.prev = p;
  }

  return;
}
