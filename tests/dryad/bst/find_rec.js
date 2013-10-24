/*@
  type tree[A] exists! l |-> tree[A] * r |-> tree[A] . { data: A, left:<l>+null, right:<r>+null } 
 */

/* lemma_nonMem :: (k:A, x:?bst[{v:A| v != k}]) => {v:void | not (Set_mem(k, keys(x, h)))}/same */

/*@ lemma_nonMem :: forall A. (k:A, x:<x>+null)/x |-> tree[{v:A | true k}] => void/same */
function lemma_nonMem(k, x){
  if (typeof(x) == "null"){
    return;
  } else {
    var xk = x.data;
    var xl = x.left;
    var xr = x.right;
    assert(k != xk);
    lemma_nonMem(k, x.left);
    lemma_nonMem(k, x.right);
    return;
  }
}

/* search :: (x:?bst[A], k:A) => {v:boolean | (Prop v) <=> Set_mem(k, keys(x, h))} */

/*@ search :: (x:<t>+null, k:number)/t |-> tree[{number | true}] => boolean/same */
function search(x, k){
  if (typeof(x) == "null"){
    return false;
  }

  var xk = x.data;
  var xl = x.left;
  var xr = x.right;

  if (k < xk){
    var t  = lemma_nonMem(k, xr);
    var x  = search(xl, k);
    return x;
  } else if (xk < k){
    var t  = lemma_nonMem(k, xl);
    var x = search(xr, k);
    return x;
  } else {
    // k == xk
    return true;
  }
}
