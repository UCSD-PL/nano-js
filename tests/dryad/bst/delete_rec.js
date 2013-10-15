//import "bst.js";
/*@
  type tree[A] exists! l |-> tree[A] * r |-> tree[A] . { data: A, left:<l>+null, right:<r>+null } 
 */

/*@
  removeRoot :: forall A. (x:{v:<t> | true})/t |-> tree[A] => <k>+null/k |-> tree[A]
*/
function removeRoot(x){
  var xl = x.left;
  var xr = x.right;

  if (typeof(xl) == "null") {
    x.right = null;
    return xr;
  } else if (typeof(xr) == "null") {
    x.left = null;
    return xl;
  } else {
   var xrl = xr.left;
 //  xr.left = null;     // extra, to cut sharing
   x.right = xrl;
   var t = removeRoot(x);
   xr.left = t;
   return xr;
  }
}

//{v:?bst[A] | keys(v) = set_minus(keys(x,h), set_singleton(k)} */

/*@ remove :: (x:<x>+null, k:number)/x |-> tree[number] => <v>+null/v |-> tree[{number | true}] */
function remove(x, k){
  if (typeof(x) == "null"){
    return null;
  }
 
  var xk = x.data;
  
  if (k < xk) {
    var xl = x.left;
    x.left = remove(xl, k);
    return x;
  } else if (xk < k) {
    var xr = x.right;
    x.right = remove(xr, k);
    return x;
  } else {
    // k == xk
    var r = removeRoot(x);
    return r;
  }
}
