//import "doubly-linked-list.js";

/*@ qualif EqNull(v:a, x:b): (((ttag v) = "null") => ((ttag x) = "null")) */
/*@ qualif EqNull(v:a, x:b): (((ttag v) != "null") => ((ttag x) != "null")) */

/* qualif EqNull(v:a, x:b, y:c): (((ttag v) = "null") => (x = y))*/
/* qualif EqNull(v:a, x:b, y:c): (((ttag v) != "null") => (x = y)) */

/* qualif EqNull(v:a, x:b): (((ttag v) = "null") => (x = null)) */
/* qualif EqNull(v:a, x:b): (((ttag v) != "null") => (x = null)) */

// fix this modulo nulls

/*@ type dlist[A,S,P] exists! l |-> dlist[A, <l>, S] . { data: A, next:<l>+null, prev:P } */

/* delete_at_middle ::  
      (u:?rdlist[A,<l>], p:<l>, v:?dlist[A,<l>])/h
      => void/ u |-> {rdlist[A,v] | keys(u) = keys(u,h)} * v |-> { dlist[A,<u>] | keys(v) = keys(v,h)} 
 */

/*@ delete_at_middle :: forall A.
      (p:<p>+null, q:{v:<q> | true}, r:<r>+null)/p |-> pp:{ data:A, next:<q>+null, prev:null }
                                    * q |-> qq:{ data:A, next:<r>+null, prev:<p>+null}
                                    * r |-> rr:dlist[A,<r>,<q>+null]
      => void/p |-> ps:{ data:A, next:<r>+null, prev:null} * r |-> rs:dlist[A,<r>,<p>+null] 
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
