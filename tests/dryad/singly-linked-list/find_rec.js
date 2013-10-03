//import "singly-linked-list.js"
/*  v=1 <=> set_mem(k, keys(x)) */

/*@ find :: forall A. (x:<l>+null,k:A)/l |-> list[A] => {v:number | (v = 1 <=> set_mem(k, keys(x))) }/same */
function find(x, k){
  if (typeof(x) != "null"){ 
    var xk = x.data; 
    if (xk == k) {
      return 1;
    } else {
      var r = find(x.next, k);
      return r;
    }
  } 
  else {
    return 0;
  }
}

