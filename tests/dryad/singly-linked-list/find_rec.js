/*@ include singly-linked-list.js */
/*@ qualif PApp(v:a): (papp1 p v) */

/*@ find :: forall < p :: (number) => prop >. 
            (x:<l>+null,k:number<p>)/l |-> xs:list[number<p>] => 
              {v:boolean | (Prop(v) <=> Set_mem(k, keysp(x,xs))) }
               /l |-> y:list[number<p>] */
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

