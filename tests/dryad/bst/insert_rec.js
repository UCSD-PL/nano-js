//import "bst.js";

/*@
insert :: forall A.
  (x:<t>+null, k:A)/t |-> ts:tree[A]
             => <r>/r |-> rs:{ tree[A] | true }
*/
function insert(x, k) {
  if (x == null)
  {
    var y   = {};
    y.data  = k;
    y.left  = null;
    y.right = null;
    return y;
  }

  var xk = x.data;
  var xl = x.left;
  var xr = x.right;

  if (cmpLT(xk, k)) {
    x.right = insert(xr, k);
  } else if (cmpLT(k, xk)) {
    x.left  = insert(xl, k);
  } 

  return x;
}
