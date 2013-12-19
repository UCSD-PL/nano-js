/*@ include bst.js */

/* qualif EqField(v:a, x:b): v = hd(x)                */
/* qualif EqField(v:a, x:b): field(v, "data") = hd(x) */
/* qualif LtField(v:a, x:b): v < field(x, "data")     */
/* qualif LtField(v:a, x:b): v > field(x, "data")     */
/* qualif EqField(v:a, x:b): v = field(x, "data")     */

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

/*@ search :: forall A. (x:<t>+null, k:A)/t |-> ts:tree[A]
                                     => {boolean | (Prop(v) <=> Set_mem(k, keysp(x,ts)))}
                                         /t |-> tss:tree[A]                                */
function search(x, k){
  if (x == null){
    return false;
  }

  var xk = x.data;
  var xl = x.left;
  var xr = x.right;

  if (cmpLT(k,xk)){
    var r  = search(xl, k);
    var t  = lemma_nonMem(k, xr);
    return r;
  } else if (cmpLT(xk,k)){
    var r = search(xr, k);
    var t = lemma_nonMem(k, xl);
    return r;
  } else {
    // k == xk
    return true;
  }
}
