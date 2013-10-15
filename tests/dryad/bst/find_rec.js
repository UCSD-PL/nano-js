
/*@ lemma_nonMem :: (k:A, x:?bst[{v:A| v != k}]) => {v:void | not (Set_mem(k, keys(x, h)))}/same */
function lemma_nonMem(k, x){
  if (x == null){
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

/*@ search :: (x:?bst[A], k:A) => {v:boolean | (Prop v) <=> Set_mem(k, keys(x, h))} */
function search(x, k){
  if (x == null){
    return false;
  }

  var xk = x.data;
  var xl = x.left;
  var xr = x.right;

  if (k < xk){
    var t  = lemma_nonMem(k, xr);
    return search(k, xl);
  }

  if (xk < k){
    var t  = lemma_nonMem(k, xl);
    return search(k, xr);
  }

  // k == xk
  return true;
}
