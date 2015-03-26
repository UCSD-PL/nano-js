/*@ include bst.js */

/* 
insert :: forall <r :: (number) => prop>.
  (x:<t>+null, k:number<r>)/t |-> ts:bst[number<r>]
      => {v:<r> | true }/r |-> rs:bst[number<r>] */
/*@ 
insert :: forall <r :: (number) => prop>.
  (x:<t>+null, k:number<r>)/t |-> ts:tree[number<r>]<{\p v -> p > v},
                                                     {\p v -> p < v}>
      => {v:<r> | true }/r |-> rs:tree[number<r>]<{\p v -> p > v},{\p v -> p < v}> 
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

  if (xk < k) {
    x.right = insert(xr, k);
  } else if (k < xk) {
    x.left  = insert(xl, k);
  }

  return x;
}