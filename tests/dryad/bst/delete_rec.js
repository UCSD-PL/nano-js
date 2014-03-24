/*@ include bst.js */

/*@ qualif NonMem(v:a):(~Set_mem(k,keysp(x,its)) && (keys(its) = keys(ots)))  */

/*@ qualif RootKeys(v:Ref):((keysp(v,ks) = keysp(field_Ref(ts,"left"),ls) ∪ keysp(field_Ref(ts,"right"),rs))
                        && (~Set_mem(field_int(ts, "data"),keysp(v,ks)))) */

/*@ qualif RootInput(v:int, x:Rec): v < field_int(x, "data") */
/*@ qualif RootInput(v:int, x:Rec): v > field_int(x, "data") */
/*@ qualif PApp(v:a): (papp1 p v) */

/*@ lemma_nonMem :: forall A B.
      (k:A, x:<x>+null)/x |-> its:tree[B]<{\x y -> x > y}, {\x y -> x < y}>
                => number/x |-> ots:tree[B]<{\x y -> x > y}, {\x y -> x < y}> */
function lemma_nonMem(k, x) {
  if (x == null){
    return 0;
  } else {
    var xk = x.data;
    var xl = x.left;
    var xr = x.right;
    lemma_nonMem(k, xl);
    lemma_nonMem(k, xr);
    return 0;
  }
}

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

/*@ remove :: forall < p :: (number) => prop >.
(t:<t>+null, k:number<p>)/t |-> in:tree[number<p>]<{\x y -> x > y}, {\x y -> x < y}> =>
                                 {v:<r>+null | (v = null || ~Set_mem(k,keys(out)))}
                                 /r |-> out:tree[number<p>]<{\x y -> x > y}, {\x y -> x < y}>
                                 */
function remove(x, k){
  if (x == null){
    return null;
  }
 
  var xk = x.data;

  if (k < xk) {
    lemma_nonMem(k, x.right);
    var xl = x.left;
    x.left = remove(xl, k);
    return x;
  } else if (xk < k) {
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
