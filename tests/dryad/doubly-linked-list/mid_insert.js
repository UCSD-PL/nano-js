/*@ include doubly-linked-list.js */

/*@ qualif Same(v:T, x:T): (len v) = (len x) */
/*@ qualif Same(v:T, x:T): (keys v) = (keys x) */

/*@ insert_at_middle ::
      (u:<a>+null, k:number, t:<b>+null)/a |-> us:{ data:number, next:{v:<b>+null | ((Prop (nil v)) <=> (Prop (nil ts)))} , prev:null }
                                       * b |-> ts:dlist[number,<b>,null]
                             => <r>+null/r |-> rs:{v:dlist[number,<r>,null] | ((~(Prop (nil us))) => ((((len v) = 2 + (len ts)))
&& ((keys v) = (Set_cup (Set_cup (Set_sng (field_int us "data")) (Set_sng k)) (keys ts)))))}

*/
function insert_at_middle (u, k, t) {
  ret = { data:k, next:t, prev:u };

  if (t != null) {
    t.prev = ret;
  }

  if (u != null) {
    u.next = ret;
    return u;
  } else {
    return ret;
  }
}
