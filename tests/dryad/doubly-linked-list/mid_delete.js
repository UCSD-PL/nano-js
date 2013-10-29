//import "doubly-linked-list.js";

/*@ qualif EqNull(v:a, x:b): (((ttag v) = "null") => ((ttag x) = "null"))   */
/*@ qualif EqNull(v:a, x:b): (((ttag v) != "null") => ((ttag x) != "null")) */
/*@ qualif EqLen(v:a, x:b): (len(v) = len(x))                               */

// fix this modulo nulls

/*@

type dlist[A,S,P] exists! l |-> ls:dlist[A, <l>, S] . me:{ data: A, next:<l>+null, prev:P }

with len(x) := (if (ttag(field(me,"next")) = "null") then 1 else (1 + len(ls)))

*/


/* delete_at_middle ::  
      (u:?rdlist[A,<l>], p:<l>, v:?dlist[A,<l>])/h
      => void/ u |-> {rdlist[A,v] | keys(u) = keys(u,h)} * v |-> { dlist[A,<u>] | keys(v) = keys(v,h)} 
 */

/*@ delete_at_middle :: forall A.
      (p:<p>+null, q:<q>, r:<r>+null)/p |-> pp:{ data:A, next:<q>+null, prev:null }
                                    * q |-> qq:{ data:A, next:<r>+null, prev:<p>+null}
                                    * r |-> rr:dlist[A,<r>,<q>+null]
                              => void/p |-> ps:{ data:A, next:<r>+null, prev:null}
                                    * r |-> rs:{dlist[A,<r>,<p>+null] | (len(v) = len(rr))}
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
