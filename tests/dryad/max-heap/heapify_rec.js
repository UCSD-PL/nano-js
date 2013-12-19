/*@ include max-heaps.js */
/*@ swapKeys :: forall A L R P Q.
  ({v:<r> | true},<n>)/r |-> r:{ left:L, key:A, right:R }
                     * n |-> n:{ left:P, key:A, right:Q }
                    => void/r |-> r2:{ left:L, key:A, right:R }
                          * n |-> n2:{ left:P, key:{A | v <= field(r2, "key")}, right:Q } */
// function swapKeys(x,c) {
//   var ck = c.key;
//   var xk = x.key;
//   if (cmpLT(xk, ck)) {
//     var t = xk;
//     xk    = ck;
//     ck    = t; 
//     c.key = ck;
//     x.key = xk;
//   }

//   return;
// }

/* qualif NNull(v:a, x:b)     : ((ttag(x)  = "null") => (ttag(v) = "null")) */
/* qualif NNull(v:a, x:b)     : ((ttag(x) != "null") => (ttag(v) != "null")) */
/* qualif Fld(v:a, x:b)       : v = field(x, "key") */
/*@ qualif FldGt(v:a, x:b, y:c): ((y != null) => (v <= field(x, "key"))) */

/*@ heapify :: forall A. ({v:<x> | true})/x |-> bs:{left:<l>+null, key:A, right:<r>+null}
                             * l |-> ls:heap[A]
                             * r |-> rs:heap[A]
                       => void/x |-> hs:heap[A]
                                    

*/                               
function heapify(x) {
  var l = x.left;
  var r = x.right;
  xk = x.data;
  
  if (l == null)  {
    if (r != null) {
      rk = r.data;
      var xk = x.key;
      var rk = r.key;
      if (cmpLT(xk, rk)) {
        r.key = xk;
        x.key = rk;
        heapify(r);
      } 
    }
    return;
  } else if (r == null) {
    if (l != null) {
      var xk = x.key;
      var lk = l.key;
      if (cmpLT(xk, lk)) {
        l.key = xk;
        x.key = lk;
        heapify(l);
      }
    }
  } else {
    var xk = x.key;
    var lk = l.key;
    var rk = r.key;
    if (cmpLT(lk,rk)) { //bug here?
      if (cmpLT(xk, rk)) {
        x.key = rk;
        r.key = xk;
        heapify(r);
      }
    } else if (cmpLT(xk, lk)) {
      x.key = lk;
      l.key = xk;
      heapify(l);
    }
  }
  return;
}
