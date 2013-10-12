import "bst.js";

/* insert :: (x:?bst[A], k:A) => {v:bst[A]| keys(v) = set_cup(keys(x), set_singleton(k))} */
function insert(x, k){
  if (x == null){
    var y   = {};
    y.data  = k;
    y.left  = null;
    y.right = null;
    return y;
  }

  var xk = x.data;

  if (k < xk){
    x.left = insert(x.left, k);
    return x;
  } 

  if (k > xk){
    x.right = insert(x.right, k);
    return x;
  }
  return x;
}
