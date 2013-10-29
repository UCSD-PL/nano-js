//import "doubly-linked-list.js";

// fix this modulo nulls
/*@ qualif EqNull(v:a, x:b): (((ttag v) = "null")  => ((ttag x) = "null"))   */
/*@ qualif EqNull(v:a, x:b): (((ttag v) != "null") => ((ttag x) != "null"))  */
/*@ qualif EqLen(v:a, x:b) : (len(v) = len(x))                               */
/*@ qualif EqLen(v:a, x:b, y:c) : ((ttag(u) != "null") => (len(v) = len(x) + len(y)))   */
/*@ qualif EqLen(v:a, x:b) : ((ttag(x) = "null") => (len(v) = 1))   */
/*@ qualif Thinger(v:a): (if (ttag(u) != "null") then (if (ttag(t) != "null") then (len(v) = len(us) + len(vs) + 1) else (len(v) = len(us) + 1)) else (if (ttag(t) != "null") then (len(v) = len(vs) + 1) else (len(v) = 1))) */

/*@
    type dlist[A,S,P] exists! l |-> ls:dlist[A, <l>, S] . me:{ data: A, next:<l>+null, prev:P }
      with
        len(x) := (if (ttag(field(me,"next")) = "null") then 1 else (1 + len(ls)))
 */

/* insert_at_middle ::  
      (u:<u>, k:A, v:<v>)/u |-> dlist[A,<u>,null] * v |-> dlist[A,<v>,null]
      => <r>/ u |-> rdlist[A,<u>,<r>] * r |-> { dlist[A,<u>] | keys(ret) = set_cup(set_singleton(k), keys(v,h))} 
 */

/* insert_at_middle :: forall A.
      (u:{<u>|true}+null, k:A, v:<v>+null)/u |-> { data:A, next:<v>+null, prev:null } * v |-> dlist[A,<v>,<u>+null]
      => <r>/r |-> { data:A, next:<v>+null, prev:null } * v |-> dlist[A,<v>+null,<r>+null]
 */

/*@ newNode :: forall A. (k:A)/emp => <x>/x |-> xs:{dlist[{A | v = k},<x>,null] | len(v) = 1} */
function newNode(k) {
    var ret = { data:k, next:null, prev:null };
    return ret;
}

/*@ insert_at_middle :: forall A.
      (u:<a>+null, k:A, t:<b>+null)/a |-> us:dlist[A,<a>,null]
                                  * b |-> vs:dlist[A,<b>,null]
                             => <r>/r |-> rs:{dlist[A,<r>,null] | (if (ttag(u) != "null") then
                                                                      (if (ttag(t) != "null") then
                                                                          (len(v) = len(us) + len(vs) + 1)
                                                                       else
                                                                          (len(v) = len(us) + 1))
                                                                      else (if (ttag(t) != "null") then
                                                                          (len(v) = len(vs) + 1)
                                                                       else
                                                                          (len(v) = 1)))}
*/
function insert_at_middle (u, k, t) {
    var ret = newNode(k);

    if (typeof(u) != "null") {
        ret.prev = u;
        u.next = ret;
    } 

    if (typeof(t) != "null") {
       t.prev = ret;
       ret.next = t;
    }

    if (typeof(u) != "null") {
        return u;
    } else {
        return ret;
    }
}
