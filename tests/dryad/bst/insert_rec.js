/*@ include bst.js */

/*@ 
insert :: forall <r :: (number) => prop>.
  (x:<t>+null, k:number<r>)/t |-> ts:tree[number<r>]<{\p v -> p > v},
                                                     {\p v -> p < v}>
      => <r>/r |-> rs:{v:tree[number<r>]<{\p v -> p > v},{\p v -> p < v}> | (keys(v) = Set_cup(Set_sng(k),keys(ts)))}
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
