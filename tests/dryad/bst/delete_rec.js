/*@ include bst.js */

/*@ qualif RApp(v:a): papp1(r, v)                             */

/*@ lemma_nonMem :: forall A B.
      (k:A, x:<x>+null)/x |-> its:tree[{B | v != k}]<{\x y -> x > y}, {\x y -> x < y}>
         => {v:void | (~Set_mem(k,keys(ots)) && (keysp(x,its) = keysp(x,ots)))}
            /x |-> ots:{v:tree[{B | v != k}]<{\x y -> x > y}, {\x y -> x < y}> | (keys(v) = keys(its))} */
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

/*@ qualif PApp(v:a) : papp1(p, v) */

/*@
  removeRoot :: forall <p :: (number) => prop>.
    (t:<t>)/t |-> ts:{ data:number, left:<l>+null, right:<r>+null }
          * l |-> ls:tree[{number<p> | v < field(ts, "data")}]<{\x y -> x > y}, {\x y -> x < y}>
          * r |-> rs:tree[{number<p> | v > field(ts, "data")}]<{\x y -> x > y}, {\x y -> x < y}>
      => {v:<k>+null | ((keysp(v,ks) = keysp(field(ts,"left"),ls) ∪ keysp(field(ts,"right"),rs))
                        && (~Set_mem(field(ts, "data"),keysp(v,ks))))}
         /k |-> ks:tree[{number<p> | v != field(ts, "data")}]<{\x y -> x > y}, {\x y -> x < y}>
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

/*@ remove :: forall <p :: (number) => prop>.
(t:<t>+null, k:number<p>)/t |-> in:tree[number<p>]<{\x y -> x > y}, {\x y -> x < y}> =>
                                 {v:<r>+null | (v = null || ~Set_mem(k,keys(out)))}
                                 /r |-> out:tree[number<p>]<{\x y -> x > y}, {\x y -> x < y}>
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
