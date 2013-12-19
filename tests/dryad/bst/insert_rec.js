/*@ include bst.js */

/*@ qualif EqKeys(v:a,h:b,ts:d): keysp(v,h) = Set_cup(Set_sng(k),keysp(v,ts)) */

/*@
insert :: forall A.
  (x:<t>+null, k:A)/t |-> ts:tree[A]
    => {v:<r> | keysp(v,rs) = Set_cup(Set_sng(k),keysp(x,ts))}/r |-> rs:tree[A] */
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
