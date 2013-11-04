/*@
  type btree[A]
       exists! l |-> lh:btree[A] * r |-> rh:btree[A]
               . me:{ left:<l>+null
                    , key:A
                    , right:<r>+null
                    }

     with hd(x)   := field(me, "key")
      and keys(x) := (if (ttag(field(me, "left")) != "null") then
                         (if (ttag(field(me, "right")) != "null") then
                             Set_cup(Set_sng(field(me, "key")), Set_cup(keys(lh),keys(rh)))
                          else
                             Set_cup(Set_sng(field(me, "key")), keys(lh)))
                      else
                         (if (ttag(field(me, "right")) != "null") then
                             Set_cup(Set_sng(field(me, "key")), keys(rh))
                          else
                             Set_sng(field(me, "key"))))
       
*/
/*@
  type heap[A]
       exists! l |-> lh:heap[{A | (v <= field(me, "key"))}]
             * r |-> rh:heap[{A | (v <= field(me, "key"))}]
               . me:{ left:<l>+null
                    , key:A
                    , right:<r>+null
                    }

     with hd(x)   := field(me, "key")
      and keys(x) := (if (ttag(field(me, "left")) != "null") then
                         (if (ttag(field(me, "right")) != "null") then
                             Set_cup(Set_sng(field(me, "key")), Set_cup(keys(lh),keys(rh)))
                          else
                             Set_cup(Set_sng(field(me, "key")), keys(lh)))
                      else
                         (if (ttag(field(me, "right")) != "null") then
                             Set_cup(Set_sng(field(me, "key")), keys(rh))
                          else
                             Set_sng(field(me, "key"))))
       
*/
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
/* qualif FldGt(v:a, x:b, y:c): ((ttag(y) != "null") => (v <= field(x, "key"))) */

/*@ heapify :: forall A. (<x>)/x |-> bs:{left:<l>+null, key:A, right:<r>+null}
                             * l |-> ls:heap[A]
                             * r |-> rs:heap[A]
                       => void/x |-> hs:{v:heap[A] | (Set_sub(keys(rs), keys(v))) }
                                    

*/                               
/*

                                                     &&(ttag(field(bs,"right")) != "null") => Set_sub(keys(rs), keys(v))
*/

function heapify(x) {
  var l = x.left;
  var r = x.right;
  xk = x.data;
  
  if (typeof(l) == "null")  {
    if (typeof(r) != "null") {
      rk = r.data;
      var xk = x.key;
      var rk = r.key;
      if (cmpLT(xk, rk)) {
        r.key = xk;
        x.key = rk;
        heapify(r);
        return;
      } 
    }
  } // else if (typeof(r) == "null") {
  //   //swapRoot(x,l);
  //   if (typeof(l) != "null") {
  //     var xk = x.key;
  //     var lk = l.key;
  //     if (cmpLT(xk, lk)) {
  //       l.key = xk;
  //       x.key = lk;
  //       heapify(l);
  //     }
  //   }
  //   return;
  // } else {
  //   var xk = x.key;
  //   var lk = l.key;
  //   var rk = r.key;
  //   if (cmpLT(lk,rk)) { //bug here?
  //     if (cmpLT(xk, rk)) {
  //       x.key = rk;
  //       r.key = xk;
  //       heapify(r);
  //     }
  //     return;
  //   } else if (cmpLT(xk, lk)) {
  //           //               swapRoot(x,l);
  //           // l = x.left;
  //     x.key = lk;
  //     l.key = xk;
  //     heapify(l);
  //     return;
  //   }
  // }
}
