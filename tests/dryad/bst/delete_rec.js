import "bst.js";

/*@ removeRoot :: (x:bst[A]) => {v:?bst[A] | keys(v) = set_minus(keys(x,h), set_singleton(root(x,h))} */

function removeRoot(k, x){
  var xl = x.left;
  var xr = x.right;
  if (xl == null){
    return xr;
  }
  if (xr == null){
    return xl;
  }
  var xrl = xr.left;
  xr.left = null;     // extra, to cut sharing
  x.right = xrl;
  xr.left = removeRoot(k, x);
  return xr;
}

/*@ remove :: (x:bst[A], k:A) => {v:?bst[A] | keys(v) = set_minus(keys(x,h), set_singleton(k)} */
function remove(x, k){
  if (x == null){
    return null;
  }
 
  var xk = x.data;
  
  if (k < xk) {
    x.left = remove(x.left, k);
    return x;
  }
  if (xk < k) {
    x.right = remove(x.right, k);
    return x;
  }
  // k == xk
  return removeRoot(x);
}
