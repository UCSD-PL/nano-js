/*@ include doubly-linked-list.js */

/*@ qualif LenPlusOne(v:a): (keys(v) = Set_cup(Set_sng(k), dkeysp(t,ts)) && (len(v) = 1 + dlenp(t,ts))) */
/*@ qualif NewKeys(v:a): (dlenp(v,xs) = 1 && dkeysp(v,xs) = Set_sng(l)) */

/*@ newNode :: forall A. (A)/emp => <x>/x |-> xs:dlist[A,<x>,null] */
function newNode(k) {
    var ret = { data:k, next:null, prev:null };
    return ret;
}

/*@ insert_at_middle :: forall A.
      (u:<a>+null, k:A, t:<b>+null)/a |-> us:{ data:A, next:<b>+null, prev:null }
                                  * b |-> ts:dlist[A,<b>,null]
                             => {v:<r>+null | ((u != null => dlenp(v,rs) = 2 + dlenp(t,ts))
                                             && u != null => dkeysp(v,rs) = Set_cup(Set_sng(field(us,"data")),Set_cup(Set_sng(k),dkeysp(t,ts))))}
                                /r |-> rs:dlist[A,<r>,null]
*/
function insert_at_middle (u, k, t) {
    var ret = newNode(k);

    if (t != null) {
      t.prev = ret;
      ret.next = t;
    }

    if (u != null) {
      ret.prev = u;
      u.next = ret;
      return u;
    } else {
      return ret;
    }
}
