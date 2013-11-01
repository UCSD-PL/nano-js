//import "bst.js";

/*@ insert :: forall A. (x:<t>+null, k:A)/t |-> ts:tree[A]
                         => <r>/r |-> rs:{tree[A] | (if (ttag(x) != "null")
                                                         then ((hd(v) = hd(ts)) && (keys(v) = Set_cup(Set_sng(k), keys(ts))))
                                                         else (((hd(v) = k))    && (keys(v) = Set_sng(k))))}                  */
function insert(x, k) {
  if (typeof(x) == "null"){
    var y   = {};
    y.data  = k;
    y.left  = null;
    y.right = null;
    return y;
  }

  var xk = x.data;

  if (cmp(k, xk)) {
    var xl = x.left;
    x.left = insert(xl, k);
    return x;
  }else {
    var xr   = x.right;
    x.right  = insert(xr, k);
    return x;
  }
}
