/*@ include doubly-linked-list.js */

/* qualif EqLen(v:T, x:T): ((v) = len(x)) */
/* qualif NNull(v:Ref, p:Ref): ((p = null) <=> (v = null)) */

/*@ delete_at_middle :: 
      (q:<q>)/p |-> pp:{ data:number, next:{v:<q>+null | ((Prop (nil v)) <=> (Prop (nil (field_Ref(qq,"prev")))))}, prev:null }
            * q |-> qq:{ data:number, next:{v:<r>+null | ((Prop (nil v)) <=> (Prop (nil rr)))}, prev:<p>+null }
            * r |-> rr:dlist[number,<r>,{v:<q>+null | ((Prop (nil v)) <=> (Prop (nil (field_Ref(qq,"next")))))}]
                              => <k>+null
                              /p |-> ps:{ data:number, next:<k>+null, prev:null } 
                             * k |-> rs:{v:dlist[number,<k>,<p>+null] | (keys v) = (keys rr) }
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
