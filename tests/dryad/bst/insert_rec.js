//import "bst.js";
/*@
  type tree[A] exists! l |-> tree[A] * r |-> tree[A] . { data: A, left:<l>+null, right:<r>+null } 
 */

/*@ insert :: (x:<t>+null, k:{number | true})/t |-> tree[number] => <r>/r |-> tree[number] */ //{v:bst[A]| keys(v) = set_cup(keys(x), set_singleton(k))}
function insert(x, k) {
  if (typeof(x) == "null"){
    var y   = {};
    y.data  = k;
    y.left  = null;
    y.right = null;
    return y;
  }

  var xk = x.data;

  if (k < xk){
    var xl = x.left;
    x.left = insert(xl, k);
    return x;
  } 

  if (k > xk){
    var xr = x.right;
    x.right = insert(xr, k);
    return x;
  }
  return x;
}
