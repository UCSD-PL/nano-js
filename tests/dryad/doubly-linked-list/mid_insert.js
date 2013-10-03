import "doubly-linked-list.js";

// fix this modulo nulls

/*@ insert_at_middle ::  
      (u:?rdlist[A,B], k:A, v:?dlist[A,C])/h 
      => <ret>/ u |-> rdlist[A,<ret>] * ret |-> { dlist[A,<u>] | keys(ret) = set_cup(set_singleton(k), keys(v,h))} 
 */
function insert_at_middle (u, k, v){
  var ret  = {};
  ret.data = k;
  ret.next = v;
  ret.prev = u;

  if (u){
    u.next = ret;
  }
  if (v){
    v.prev = ret;
  }
  return ret;
}
