/*@ include red-black.js */

/*@ is_red :: forall A.
                (x:<t>+null)/t |-> in:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
                  => ret:{b:boolean | (((Prop b) <=> (colorp(x,in) != 0))
                      && (colorp(x,out) = colorp(x,in))
                      && (bheightp(x,out) = bheightp(x,in)))}/t |-> out:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>  */


/*@ deleteKey :: forall A.
      (x:<x>+null, { k:A | (x = null || Set_mem(k, keys(in))) } )/x |-> in:rbtree[A]<{\h v -> v < h},{\h v -> v > h}>
        => { v:<t>+null | true }/t |-> out:rbtree[A]<{\h v -> v < h},{\h v -> v > h}>                                            */
// function deleteKey(x, k) {
//   if (x == null) {
//     return null;
//   }
  
//   var xl = x.left;
//   var xr = x.right;
//   var xk = x.key;
//   var xc = x.color;
  
//   if (xk == k) {
//     if (xl == null && xr == null) {
//       return null;
//     } else if (xl == null) {
//       return xr;
//     } else if (xr == null) {
//       return xl;
//     } else {
//       assume(false);
//       return x;
//     }
//   } else {
//     assume(false);
//     return x;
//   }
// }
function deleteKey (x,t) {

}

function del (x,k) {
  if (x == null) {
    return x;
  } else {
    var xk = x.key;
    if (xk == k) {
      var xl = x.left;
      var xr = x.right;
      var r = append(xl, xr);
    }
  }
}
