/*@ include bst.js */

/*@ lemma_nonMem :: forall A B.
      (k:A, x:<x>+null)/x |-> its:tree[{B | v != k}]
         => {v:void | ((~(Set_mem(k, keys(ots)))))}
            /x |-> ots:{tree[{B | v != k}] | (keys(v) = keys(its)
                                           && hd(v) = hd(its)
                                           && (hd(v) != k || x = null)) } */
function lemma_nonMem(k, x) {
  if (x == null){
    return;
  } else {
    var xk = x.data;
    var xl = x.left;
    var xr = x.right;
    return;
  }
}

/*@
  removeRoot :: forall A.
    (t:<t>)/t |-> ts:{ data:A, left:<l>+null, right:<r>+null }
          * l |-> ls:tree[{A | v < field(ts, "data")}]
          * r |-> rs:tree[{A | v > field(ts, "data")}]
      => {v:<k>+null | (keysp(v,ks) = Set_cup(keysp(field(ts,"left"),ls),
                                              keysp(field(ts,"right"),rs))
                     && (~(Set_mem(field(ts, "data"),keysp(field(ts,"left"),ls))))
                     && (~(Set_mem(field(ts, "data"),keysp(field(ts,"right"),rs))))
                                              )}
         /k |-> ks:tree[{A | v != field(ts, "data")}]
*/
function removeRoot(t){
  var tl = t.left;
  var tr = t.right;
  var tk = t.data;

  if (tl == null) {
    t.right = null;
    lemma_nonMem(tk, tr);
    return tr;
  } else if (tr == null) {
    t.left = null;
   lemma_nonMem(tk, tl);
    return tl;
  } else {
   var trl = tr.left;
   var trk = tr.data;
   tr.left = null;     // extra, to cut sharing
   t.right = trl;
   t = removeRoot(t);
   tr.left = t;
   lemma_nonMem(tk, tr);
   return tr;
  }
}

/*@ remove :: forall A. (t:<t>+null, k:A)/t |-> in:tree[A] =>
                                 {v:<r>+null | (v = null || (~(Set_mem(k,keys(out)))))}
                                 /r |-> out:tree[A]
                                 */
function remove(x, k){
  if (x == null){
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
    var r = removeRoot(x);
    return r;
  }
}
