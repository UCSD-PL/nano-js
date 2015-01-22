/*@ include bst.js */

/* lemma_nonMem :: forall A B.
      (k:A, x:<x>+null)/x |-> its:tree[B]<{\x y -> true}, {\x y -> true}>
              => number/x |-> ots:tree[B]<{\x y -> true}, {\x y -> true}>   */
// function lemma_nonMem(k, x) {
//  if (x == null){
//    return 0;
//  } else {
//    var xk = x.data;
//    var xl = x.left;
//    var xr = x.right;
//    lemma_nonMem(k, xl);
//    lemma_nonMem(k, xr);
//    return 0;
//  }
// }


/*@ search :: forall <p :: (number) => prop>.
     (x:<t>+null, k:number<p>)/t |-> ts:tree[number<p>]<{\x y -> x > y}, {\x y -> x < y}>
        => {v:boolean | ((Prop v) => (Set_mem k (keysp x tss))) }
           /t |-> tss:tree[number<p>]<{\x y -> x > y}, {\x y -> x < y}>       */
function search(x, k){
  if (x == null){
    return false;
  }

  var xk = x.data;
  var xl = x.left;
  var xr = x.right;
  if (k < xk){
    var r = search(xl, k);
    return r;
  } else if (xk < k){
    var r = search(xr, k);
    return r;
  } else {
    // k == xk
    return true;
  }
}
