/*@ include max-heaps.js */

/*@ qualif FldGt(v:a, y:Ref, x:Rec): ((y != null) =>  (v <= (field_int x "key")))    */
/*@ qualif RApp(v:a): papp1(r,v)                                            */

/*@ heapify :: forall < r :: (number) => prop >.
 ({v:<x> | true})/x |-> bs:{left:<l>+null, key:number<r>, right:<r>+null}
                             * l |-> ls:tree[number<r>]<{\p v -> v <= p},{\p v -> v <= p}>
                             * r |-> rs:tree[number<r>]<{\p v -> v <= p},{\p v -> v <= p}>
                       => void/x |-> hs:tree[number<r>]<{\p v -> v <= p},{\p v -> v <= p}>
                                    

*/                               
function heapify(x) {
  var l = x.left;
  var r = x.right;
  xk = x.data;
  
  if (l == null)  {
    if (r != null) {
      var xk = x.key;
      var rk = r.key;
      if (xk < rk) {
        r.key = xk;
        x.key = rk;
        heapify(r);
        return;
      }
    }
  } else {
    if (r == null) {
      if (l != null) {
      var xk = x.key;
        var lk = l.key;
        if (xk < lk) {
          l.key = xk;
          x.key = lk;
          heapify(l);
          return;
        }
      }
    } else {
      var xk = x.key;
      var lk = l.key;
      var rk = r.key;
      if (lk < rk) { //bug here?
        if (xk < rk) {
          x.key = rk;
          r.key = xk;
          heapify(r);
          return;
        }
      } else if (xk < lk) {
        x.key = lk;
        l.key = xk;
        heapify(l);
        return;
      }
    }
    return;
  }
}
