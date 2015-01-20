/*@ include doubly-linked-list.js */

/*@ qualif Same(v:Ref,vs:T): (dkeysp(v,vs) = dkeysp(t,ts)
                          && dlenp(v,vs) = dlenp(t,ts)) */
/*@ qualif Field(v:a): v = field_int(us, "data") */


// /*@ insert_at_middle2 ::
//   (u:{v:<a> | true},k:number,t:<b>)/a |-> as:dlist[number,<a>,<b>] * b |-> bs:dlist[number,<b>,<a>]
//   => <r>/r |-> dlist[number,<r>,<a>] * a |-> as:dlist[number,<a>,<r>] */
// function insert_at_middle2(u,k,t) {
//   ret = { data:k, next:t, prev:u };
//   u.prev = ret;
//   t.prev = ret;
//   return ret;
// }

/*@ insert_at_middle ::
      (u:<a>+null, k:number, t:<b>+null)/a |-> us:{ data:number, next:<b>+null, prev:null }
                                       * b |-> ts:dlist[number,<b>,null]
                             => {v:<r>+null | ((u != null => (dlenp(v,rs) = 2 + dlenp(t,ts)))
                                             &&(u != null => (dkeysp(v,rs) = Set_cup(Set_sng(field_int(us,"data")),Set_cup(Set_sng(k),dkeysp(t,ts))))))}
                                /r |-> rs:dlist[number,<r>,null]
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
