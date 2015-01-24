/*@ include singly-linked-list.js */

/*@ find :: forall A. 
  (x:{v:<l>+null | (Prop(nil(v)) => Prop(nil(xs)))}, k:A)/l |-> xs:list[A] => 
  {v:boolean | (Prop(v) <=> Set_mem(k, keys(y))) }
  /l |-> y:{v:list[A] | (Prop(nil(xs)) => Prop(nil(v)))}  */
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

