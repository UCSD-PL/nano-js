//import "doubly-linked-list.js";

// fix this modulo nulls

/*@ type dlist[A,S,P] exists! l |-> dlist[A, <l>, S] . { data: A, next:<l>+null, prev:P } */

/* insert_at_middle ::  
      (u:<u>, k:A, v:<v>)/u |-> dlist[A,<u>,null] * v |-> dlist[A,<v>,null]
      => <r>/ u |-> rdlist[A,<u>,<r>] * r |-> { dlist[A,<u>] | keys(ret) = set_cup(set_singleton(k), keys(v,h))} 
 */

/*@ insert_at_middle :: forall A.
      (u:{<u>|true}, k:A, v:<v>)/u |-> { data:A, next:<v>, prev:null } * v |-> dlist[A,<v>,<u>]
      => <r>/u |-> { data:A, next:<r>, prev:null } * r |-> dlist[A,<r>,<u>]
 */
function insert_at_middle (u, k, v){
  var ret  = {};
  ret.data = k;
  ret.next = v;
  ret.prev = u;

  if (typeof(u) != "null") {
      u.next = ret;
  }

  if (typeof(v) != "null") {
      v.prev = ret;
  }

  return ret;
}
