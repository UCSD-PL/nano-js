import "doubly-linked-list.js";

// fix this modulo nulls

/*@ delete_at_middle ::  
      (u:?rdlist[A,<l>], p:<l>, v:?dlist[A,<l>])/h
      => void/ u |-> {rdlist[A,v] | keys(u) = keys(u,h)} * v |-> { dlist[A,<u>] | keys(v) = keys(v,h)} 
 */
function delete_at_middle (u, p, v){
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
