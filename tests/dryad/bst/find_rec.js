/*@ qualif LtField(v:a, x:b): v < field(x, "data")     */
/*@ qualif LtField(v:a, x:b): v > field(x, "data")     */
/*@ qualif EqField(v:a, x:b): v = field(x, "data")     */
/*@ qualif EqField(v:a, x:b): v = hd(x)                */
/*@ qualif EqField(v:a, x:b): field(v, "data") = hd(x) */

/* lemma_nonMem :: (k:A, x:?bst[{v:A| v != k}]) => {v:void | not (Set_mem(k, keys(x, h)))}/same */

/*@ lemma_nonMem :: forall A. (k:A, x:<x>+null)/x |-> its:tree[{A | v != k}]
                                        => {v:void | ((~(Set_mem(k, keys(its)))))}
                                               /x |-> ots:{tree[{A | v != k}] | ((ttag(x) != "null") => ((keys(v) = keys(its)) && (hd(v) = hd(its)))) } */
function lemma_nonMem(k, x){
  if (typeof(x) == "null"){
    return;
  } else {
    var xk = x.data;
    var xl = x.left;
    var xr = x.right;
    assert(k != xk);
    return;
  }
}

/*@ cmpLT :: forall A. (x:A, y:A) => {v:boolean | (Prop(v) <=> (x < y))} */
/* search :: (x:?bst[A], k:A) => {v:boolean | (Prop v) <=> Set_mem(k, keys(x, h))} */

/*@ search :: forall A. (x:<t>+null, k:A)/t |-> ts:tree[A]
                                     => {boolean | (if (ttag(x) = "null")
                                                       then (~(Prop(v)))
                                                       else (Prop(v) <=> Set_mem(k, keys(ts))))}/ */
function search(x, k){
  if (typeof(x) == "null"){
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
