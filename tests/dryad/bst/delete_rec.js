//import "bst.js";
/*@ lemma_nonMem :: forall A B. (k:A, x:<x>+null)/x |-> its:tree[{B | v != k}]
                                        => {v:void | ((~(Set_mem(k, keys(its)))))}
                                               /x |-> ots:{tree[{B | v != k}] | ((keys(v) = keys(its))
                                                                              && (hd(v) = hd(its))) } */
function lemma_nonMem(k, x){
  if (typeof(x) == "null"){
    return;
  } else {
    var xk = x.data;
    var xl = x.left;
    var xr = x.right;
    return;
  }
}

/*@
  removeRoot :: forall A. (x:<t>)/t |-> ts:{ data:A, left:<l>+null, right:<r>+null}
                                * l |-> ls:tree[{A | v < field(ts, "data")}]
                                * r |-> rs:tree[{A | v > field(ts, "data")}]
 =>                      {v:<k>+null | ((ttag(v) = "null") <=>
                                        ((ttag(field(ts, "left")) = "null")
                                      && (ttag(field(ts, "right")) = "null")))}
                                 /k |-> ks:{tree[A] | (if (ttag(field(ts, "left")) = "null")
                                                           then (if (ttag(field(ts, "right")) = "null")
                                                                    then true 
                                                                    else (keys(v) = keys(rs)))
                                                           else (if (ttag(field(ts, "right")) = "null")
                                                                    then (keys(v) = keys(ls))
                                                                    else (keys(v) = Set_cup(keys(rs), keys(ls)))))}
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
   xr.left = null;     // extra, to cut sharing
   x.right = xrl;
   var t = removeRoot(x);
   xr.left = t;
   return xr;
  }
}

//{v:?bst[A] | keys(v) = set_minus(keys(x,h), set_singleton(k)} */

/*@ remove :: forall A. (x:<x>+null, k:A)/x |-> it:tree[A] =>
                                 {v:<v>+null | ((ttag(v) = "null") => ((ttag(x) = "null") || (hd(it) = k)))}
                                 /v |-> ot:{tree[A] | ((ttag(lqreturn) != "null") =>
                                                       (~(Set_mem(k, keys(v)))))}
                                 */
function remove(x, k){
  if (typeof(x) == "null"){
    return null;
  }
 
  var xk = x.data;

  if (cmpLT(k,xk)) {
    lemma_nonMem(k, x.right);
    var xl = x.left;
    x.left = remove(xl, k);
    return x;
  } else if (cmpLT(xk,k)) {
    lemma_nonMem(k, x.left);
    var xr = x.right;
    x.right = remove(xr, k);
    return x;
  } else {
    // k == xk
    lemma_nonMem(k, x.left);
    lemma_nonMem(k, x.right);
    var r = removeRoot(x);
    return r;
  }
}
