/*@ include bst.js */

/*@ qualif RootInput(v:int, x:Rec): v < field_int(x, "data") */
/*@ qualif RootInput(v:int, x:Rec): v > field_int(x, "data") */

/*@
  removeRoot :: forall A B. 
    (t:<t>)/t |-> ts:{ data:A, left:<l>+null, right:<r>+null }
          * l |-> ls:tree[B]<{\x y -> x > y}, {\x y -> x < y}>
          * r |-> rs:tree[B]<{\x y -> x > y}, {\x y -> x < y}>
      => v:<k>+null/k |-> ks:tree[B]<{\x y -> x > y}, {\x y -> x < y}>
*/
function removeRoot(t){
  var tl = t.left;
  var tr = t.right;
  var tk = t.data;

  if (tl == null) {
    t.right = null;
    return tr;
  } else if (tr == null) {
    t.left = null;
    return tl;
  } else {
    var trl = tr.left;
    var trk = tr.data;
    tr.left = null;     // extra, to cut sharing
    t.right = trl;
    t = removeRoot(t);
    tr.left = t;
    return tr;
  }
}

/*@ remove :: forall < p :: (number) => prop >.
(t:<t>+null, k:number<p>)/t |-> in:tree[number<p>]<{\x y -> x > y}, {\x y -> x < y}> =>
                                 {v:<r>+null | true }
                                 /r |-> out:tree[number<p>]<{\x y -> x > y}, {\x y -> x < y}>
                                 */
function remove(x, k){
  if (x == null){
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
