/*@ include doubly-linked-list.js */

/*@ qualif EqLen(v:a, x:b): (len(v) = len(x)) */
/*@ qualif NNull(v:a): ((p != null) => (v = r)) */

/*@ delete_at_middle :: 
      (p:<p>+null, q:<q>, r:<r>)/p |-> pp:{ data:number, next:<q>+null, prev:null     }
                                    * q |-> qq:{ data:number, next:<r>+null, prev:<p>+null }
                                    * r |-> rr:dlist[number,<r>,<q>+null]
                              => void/p |-> ps:{ data:number, next:<r>+null, prev:null }
                                    * r |-> rs:{v:dlist[number,<r>,<p>+null] | true    }
 */
function delete_at_middle (p,q,r) {
  q.next = null;
  q.prev = null;

  delete(q);

  // if (p == null && r == null) {
  //   return;
  // }
  
  // if (r != null) {
    r.prev = p;
    if (p != null) {
      p.next = r;
      return;
    } else {
      return;
    }
  // } else {
  //     return;
  //   }
}
