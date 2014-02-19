/*@ include singly-linked-list.js */

/*@ find :: forall A. 
  (x:<l>+null,k:A)/l |-> xs:list[A] => 
  {v:boolean | (Prop(v) <=> Set_mem(k, keysp(x,y))) }
  /l |-> y:list[A] */
function find(x, k){
  if (x != null){ 
    var xk = x.data; 
    if (xk == k) {
      return true;
    } else {
      r = find(x.next, k);
      return r;
    }
  }
  return false;
}

