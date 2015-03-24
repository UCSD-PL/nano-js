/*@ include max-heaps.js */

/*@ qualif FldGt(v:Rec, y:number, x:Rec): ((~ (Prop (nil y))) =>  (y <= (field_int x "key")))  */
/*@ qualif RApp(v:a): papp1(q,v)                                                     */

/*@ heapify :: forall < q :: (number) => prop >.
 (x:{v:<x> | true})/x |-> bs:{ left:{v:<l>+null | ((Prop (nil v)) => (Prop (nil ls)))}
                             , key:number<q>
                             , right:{v:<r>+null | ((Prop (nil v)) => (Prop (nil rs)))}
                             }
                  * l |-> ls:tree[number<q>]<{\p v -> v <= p},{\p v -> v <= p}>
                  * r |-> rs:tree[number<q>]<{\p v -> v <= p},{\p v -> v <= p}>
            => void/x |-> hs:{v:tree[number<q>]<{\p v -> v <= p},{\p v -> v <= p}> | (keys(v) = (Set_cup (Set_cup (Set_sng (field_int bs "key"))
                                                                                                                  (keys ls))
                                                                                                         (keys rs)))}
                                    

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
      } else { return; }
    } else { return; }
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
        } else { return; }
      } else { return; }
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
  }
  return;
}
