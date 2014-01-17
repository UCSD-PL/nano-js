/*@ include bst.js */

/*@ qualif RApp(v:a): papp1(r, v)                             */

/*@ lemma_nonMem :: forall A B.
      (k:A, x:<x>+null)/x |-> its:tree[{B | v != k}]<{\x y -> x > y}, {\x y -> x < y}>
         => {v:void | (((~(Set_mem(k, keys(ots))))) && (keysp(x,its) = keysp(x,ots)))}
            /x |-> ots:{v:tree[{B | v != k}]<{\x y -> x > y}, {\x y -> x < y}> | (keys(v) = keys(its))} */
function lemma_nonMem(k, x) {
  if (x == null){
    return;
  } else {
    var xk = x.data;
    var xl = x.left;
    var xr = x.right;
    return;
  }
}

/*@ search :: forall < r :: (number) => prop >.
     (x:<t>+null, k:number<r>)/t |-> ts:tree[number<r>]<{\x y -> x > y}, {\x y -> x < y}>
        => {boolean | ((keysp(x,ts) = keysp(x,tss)) && (Prop(v) <=> Set_mem(k, keysp(x,ts))))}
          /t |-> tss:tree[number<r>]<{\x y -> x > y}, {\x y -> x < y}>   */
function search(x, k){
  if (x == null){
    return false;
  }

  var xk = x.data;
  var xl = x.left;
  var xr = x.right;

  if (k < xk){
    var r = search(xl, k);
    lemma_nonMem(k, xr);
    return r;
  } else if (k > xk){
    var r = search(xr, k);
    lemma_nonMem(k, xl);
    return r;
  } else {
    // k == xk
    return true;
  }
}
