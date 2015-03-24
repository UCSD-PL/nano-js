/*@ include bst.js */

/*@ qualif NonMem(v:a):(~Set_mem(k,keysp(x,its)) && (keys(its) = keys(ots)))  */
/*@ qualif RootKeys(v:a):((keysp(v,ks) = keysp(field(ts,"left"),ls) ∪ keysp(field(ts,"right"),rs))
                        && (~Set_mem(field(ts, "data"),keysp(v,ks)))) */
/*@ qualif RootInput(v:a): v < field(ts, "data") */
/*@ qualif RootInput(v:a): v > field(ts, "data") */
/*@ qualif PApp(v:a): (papp1 p v) */
/*@ qualif RApp(v:a): (papp1 r v)                                             */
/*@ qualif EqKeys(v:a,h:b): keys(v) = keysp(x,h) ∪1 k         */
/*@ qualif NonMem(v:a):(~Set_mem(k,keysp(x,its)) && (keys(its) = keys(ots)))  */

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
/*@ include bst.js */

/*@ search :: forall < r :: (number) => prop >.
     (x:<t>+null, k:number<r>)/t |-> ts:tree[number<r>]<{\x y -> x > y}, {\x y -> x < y}>
        => {v:boolean | ((true || keysp(x,ts) = keysp(x,tss)) 
                      && (Prop(v) <=> Set_mem(k, keysp(x,ts))))}
           /t |-> tss:tree[number<r>]<{\x y -> x > y}, {\x y -> x < y}>       */
function search(x, k){
  if (x == null){
    return false;
  }

  var xk = x.data;
  var xl = x.left;
  var xr = x.right;
  if (k < xk){
    var r = search(xl, k);
    lemma_nonMem(k, xr);
    return r;
  } else if (xk < k){
    var r = search(xr, k);
    lemma_nonMem(k, xl);
    return r;
  } else {
    // k == xk
    return true;
  }
}
/*@ include bst.js */
/*@ 
insert :: forall <r :: (number) => prop>.
  (x:<t>+null, k:number<r>)/t |-> ts:tree[number<r>]<{\p v -> p > v},
                                                     {\p v -> p < v}>
      => {v:<r> | (keysp v rs) = (keysp x ts) ∪1 k}/r |-> rs:tree[number<r>]<{\p v -> p > v},
                                                                             {\p v -> p < v}> */
function insert(x, k) {
  if (x == null)
  {
    var y   = {};
    y.data  = k;
    y.left  = null;
    y.right = null;
    return y;
  }

  var xk = x.data;
  var xl = x.left;
  var xr = x.right;

  if (xk == k)
    return x;

  if (xk < k) {
    x.right = insert(xr, k);
    return x;
  } else {
    x.left  = insert(xl, k);
    return x;
  }
}
