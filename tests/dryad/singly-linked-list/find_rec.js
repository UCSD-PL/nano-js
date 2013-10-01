import "singly-linked-list.js"

/*@ find :: (x:list[A], k:A) => {v:number|v=1 <=> set_mem(k, keys(x))} */
function find(x, k){
  if (x){ 
    var xk = x.data; 
    if (xk == k){
      return 1;
    } else {
      return find(x.next, k);
    }
  } 
  else {
    return 0;
  }
}

