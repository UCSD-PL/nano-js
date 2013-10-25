//import "doubly-linked-list.js";

// fix this modulo nulls
/* qualif EqNull(v:a, x:b): (((ttag v) = "null") => ((ttag x) = "null")) */
/* qualif EqNull(v:a, x:b): (((ttag v) != "null") => ((ttag x) != "null")) */
/* qualif EqNull(v:a, x:b, y:c): (((ttag x) != "null") => (v = y)) */
/* qualif EqNull(v:a, x:b, y:c): (((ttag x) = "null") => (v = y)) */

/*@ type dlist[A,S,P] exists! l |-> dlist[A, <l>, S] . { data: A, next:<l>+null, prev:P } */

/* insert_at_middle ::  
      (u:<u>, k:A, v:<v>)/u |-> dlist[A,<u>,null] * v |-> dlist[A,<v>,null]
      => <r>/ u |-> rdlist[A,<u>,<r>] * r |-> { dlist[A,<u>] | keys(ret) = set_cup(set_singleton(k), keys(v,h))} 
 */

/* insert_at_middle :: forall A.
      (u:{<u>|true}+null, k:A, v:<v>+null)/u |-> { data:A, next:<v>+null, prev:null } * v |-> dlist[A,<v>,<u>+null]
      => <r>/r |-> { data:A, next:<v>+null, prev:null } * v |-> dlist[A,<v>+null,<r>+null]
 */

/*@ newNode :: forall A. (k:A)/emp => <x>/x |-> xs:dlist[{A | v = k},<x>,null] */
function newNode(k) {
    var ret = { data:k, next:null, prev:null };
    return ret;
}

/*@ insert_at_middle :: forall A.
      (u:{<a>|true}+null, k:A, s:{v:<b>| true}+{null | false})/a |-> us:dlist[A,<a>,null] * b |-> vs:dlist[A,<b>,null]
      => <r>/r |-> rs:dlist[A,<r>,null]
*/
function insert_at_middle (u, k, s) {
    var ret = newNode(k);

    if (typeof(u) != "null") {
        ret.prev = u;
        u.next = ret;
    } 

    if (typeof(s) != "null") {
       s.prev = ret;
       ret.next = s;
    }

    if (typeof(u) != "null") {
        return u;
    } else {
        return ret;
    }
}
