/*@ include doubly-linked-list.js */

/*@ qualif EqLen(v:a, x:b): (len(v) = len(x)) */
/*@ qualif NNull(v:a, p:b): ((p = null) <=> (v = null)) */
/*@ qualif NNull(v:a): (v = null) */

/*@ delete_at_middle :: 
      (q:<q>)/p |-> pp:{ data:number, next:{v:<q>+null | ((v = null) <=> (field(qq,"prev") = null))}, prev:null }
            * q |-> qq:{ data:number, next:<r>+null, prev:{v:<p>+null | ((v = null) <=> (field(pp,"next") = null)) }}
            * r |-> rr:dlist[number,<r>,{v:<q>+null | ((v = null) <=> (field(qq,"next") = null))}]
                              => <k>+null/p |-> ps:{ data:number, next:<k>+null, prev:null }
                                        * k |-> rs:dlist[number,<k>,<p>+null]
 */
function delete_at_middle (q) {
  var p = q.prev;
  var r = q.next;

  q.prev = null;
  q.next = null;

  if (p != null) {
    p.next = r;
  }
  
  if (r != null) {
    r.prev = p;
    return r;
  } else {
    return r;
  }

}
