//import "doubly-linked-list.js";

// fix this modulo nulls

/*@ type dlist[A,S,P] exists! l |-> dlist[A, <l>, S] . { data: A, next:<l>+null, prev:P } */

/* insert_at_middle ::  
      (u:<u>, k:A, v:<v>)/u |-> dlist[A,<u>,null] * v |-> dlist[A,<v>,null]
      => <r>/ u |-> rdlist[A,<u>,<r>] * r |-> { dlist[A,<u>] | keys(ret) = set_cup(set_singleton(k), keys(v,h))} 
 */

/* insert_at_middle :: forall A.
      (u:{<u>|true}+null, k:A, v:<v>+null)/u |-> { data:A, next:<v>+null, prev:null } * v |-> dlist[A,<v>,<u>+null]
      => <r>/r |-> { data:A, next:<v>+null, prev:null } * v |-> dlist[A,<v>+null,<r>+null]
 */

/*@ insert_at_middle :: forall A.
      (u:{<u>|true}+null, k:A, s:{<v>| true}+null)/u |-> { data:A, next:<v>, prev:null } * v |-> dlist[A,<v>,<u>+null]
      => <r>/r |-> dlist[A,<r>,null]
 */
function insert_at_middle (u, k, s) {
  if (typeof(u) == "null") {
      var ret  = {};
      ret.data = k;
      ret.next = s;
      ret.prev = null;

      if (typeof(s) != "null") {
          s.prev = ret;
      }

      return ret;
  } else {
      return null;
      // return u;
  }
   /* else {
      var ret  = {};
      ret.data = k;
      ret.next = v;
      ret.prev = u;
      u.next = ret;
      if (typeof(v) != "null") {
         v.prev = ret; 
      }
      return ret;
  }*/

  // if (typeof(u) != "null") {
  //     u.next = ret;
  // }

  // if (typeof(v) != "null") {
  //     v.prev = ret;
  // }

  // return ret;
}