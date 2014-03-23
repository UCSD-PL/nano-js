/*@ include doubly-linked-list.js */

/*@ qualif Same(v:a,vs:b): (dkeysp(v,vs) = dkeysp(t,ts)
                          && dlenp(v,vs) = dlenp(t,ts)) */
/*@ qualif Field(v:x): v = field(us, "data") */


/*@ insert_at_middle ::
      (u:<a>+null, k:number, t:<b>+null)/a |-> us:{ data:number, next:<b>+null, prev:null }
                                       * b |-> ts:dlist[number,<b>,null]
                             => {v:<r>+null | ((u != null => (dlenp(v,rs) = 2 + dlenp(t,ts)))
                                             &&(u != null => (dkeysp(v,rs) = Set_cup(Set_sng(field(us,"data")),Set_cup(Set_sng(k),dkeysp(t,ts))))))}
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
