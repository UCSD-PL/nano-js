/*@ include red-black.js */

/*@ is_red :: forall A.
                (x:<t>+null)/t |-> tin:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
                  => {b:boolean | (((Prop b) <=> (colorp(x,tout) != 0))
                                    && (colorp(x,tout) = colorp(x,tin))
                                    && (bheightp(x,tout) = bheightp(x,tin)))}
                      /t |-> tout:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>  */
function is_red(x) 
{
  if (x == null) 
  {
    return false;
  } 
  else 
  {
    var xc = x.color; 
    return (xc != 0);
  }
}

/*@ qualif Foo(v:a): (v < field(bl,"key") && v < field(bt,"key")) */
/*@ qualif Foo(v:a): (v > field(bl,"key") && v < field(bt,"key")) */

/*@ qualif Foo(v:a): (v < field(br,"key") && v > field(bt,"key")) */
/*@qualif Foo(v:a): (v > field(br,"key") && v > field(bt,"key")) */

/*@
  lbal :: forall A.
    (t:{v:<t> | true})/
            lr |-> blr:rbtree[{v:A | (v > field(bl,"key") && v < field(bt,"key"))}]<{\x y -> x > y},{\x y -> x < y}>
          * ll |-> bll:rbtree[{v:A | (v < field(bl,"key") && v < field(bt,"key"))}]<{\x y -> x > y},{\x y -> x < y}>
          * r  |-> br:rbtree[{v:A | v > field(bt, "key")}]<{\x y -> x > y},{\x y -> x < y}>
          * l  |-> bl:{ color:number 
                      , key:{v:A | v < field(bt, "key")}
                      , left:{v:<ll>+null | (bheightp(v,bll)  = bheightp(field(bl,"right"),blr)) }
                      , right:{v:<lr>+null | (bheightp(v,blr) = bheightp(field(bl,"left"),bll)) }
                     }
          * t |-> bt:{ color:number
                     , key:{v:A | v > field(bl, "key")}
                     , left:{v:<l>+null | (bheightp(field(bt,"right"),br) = (if (v = null) then 1 else (bheightp(field(bl,"left"),bll) + (if (field(bl,"color") = 0) then 1 else 0)))) }
                     , right:{v:<r>+null | (bheightp(v,br) = (if (field(bt,"left") = null) then 1 else (bheightp(field(bl,"right"),blr) + (if (field(bl,"color") = 0) then 1 else 0)))) }
                     }
         => {v:<x> | (((field(bl,"color") = 0) => (colorp(v,out) = 0))
                    && (bheightp(v,out) = 1 + bheightp(field(bt,"right"),br)))}
            /x |-> out:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
*/
// function lbal(t) {
//   var tc = t.color;
//   var l  = t.left;
//   var r  = t.right;
//   if (l != null) {
//     var lc = l.color;
//     if (lc != 0) {
//       var ll = l.left;
//       var lr = l.right;
//       if (is_red(ll)) {
//         t.left   = l.right;
//         l.right  = t;
//         t.color  = 0;
//         ll.color = 0;
//         l.color  = 1;
//         return l;
//       } else {
//         if (is_red(lr)) {
//           l.right = lr.left;
//           lr.left = l;
//           t.left = lr.right;
//           lr.right = t;
//           l.color  = 0;
//           t.color  = 0;
//           lr.color = 1;
//           return lr;
//         } else {
//           t.color = 0;
//           return t;
//         }
//       }
//     } else {
//       t.color = 0;
//       return t;
//     }
//   } else {
//     t.left = null;
//     t.color = 0;
//     return t;
//   }
// }

/*@ qualif Foo(v:a): (v > field(lbt,"key")) */
/*@ qualif Foo(v:a): (v < field(lbt,"key")) */
/*@ qualif Foo(v:a): (v > field(lbl,"key")) */
/*@ qualif Foo(v:a): (v < field(lbl,"key")) */

/*@
  rbal :: forall A.
    (t:{v:<t> | true})/
            rr |-> brr:rbtree[{v:A | (v > field(br,"key") && v > field(bt,"key"))}]<{\x y -> x > y},{\x y -> x < y}>
          * rl |-> brl:rbtree[{v:A | (v < field(br,"key") && v > field(bt,"key"))}]<{\x y -> x > y},{\x y -> x < y}>
          * l  |-> bl: rbtree[{v:A | v < field(bt, "key")}]<{\x y -> x > y},{\x y -> x < y}>
          * r  |-> br: { color:number
                       , key:  {v:A | v > field(bt, "key")}
                       , left: {v:<rl>+null | (bheightp(v,brl)  = bheightp(field(br,"right"),brr)) }
                       , right:{v:<rr>+null | (bheightp(v,brr) = bheightp(field(br,"left"),brl)) }
                       }
          * t |-> bt:{ color:number
                     , key:A
                     , left:{v:<l>+null | (bheightp(v,bl) = (if (field(bt,"right") = null) then 1 else (
                     (bheightp(field(br,"right"),brr) + (if (field(br,"color") = 0) then 1 else 0))))) }
                     , right:{v:<r>+null | (bheightp(field(bt,"left"),bl) = (if (v = null) then 1 else (bheightp(field(br,"left"),brl) + (if (field(br,"color") = 0) then 1 else 0)))) }
                     }
         => {v:<x> | (((field(br,"color") = 0) => (colorp(v,out) = 0))
                    && (bheightp(v,out) = 1 + bheightp(field(bt,"left"),bl)))}
            /x |-> out:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>

*/


/*@
  lbalS :: forall A.
    (t:{v:<t> | true})/
            lr |-> lblr:rbtree[{v:A | (v > field(lbl,"key") && v < field(lbt,"key"))}]<{\x y -> x > y},{\x y -> x < y}>
          * ll |-> lbll:rbtree[{v:A | (v < field(lbl,"key") && v < field(lbt,"key"))}]<{\x y -> x > y},{\x y -> x < y}>
          * r  |-> lbr:rbtree[{v:A | v > field(lbt, "key")}]<{\x y -> x > y},{\x y -> x < y}>
          * l  |-> lbl:{ color:number
                      , key:{v:A | v < field(lbt, "key")}
                      , left:{v:<ll>+null | (bheightp(v,lbll)  = bheightp(field(lbl,"right"),lblr)) }
                      , right:{v:<lr>+null | (bheightp(v,lblr) = bheightp(field(lbl,"left"),lbll)) }
                     }
          * t |-> lbt:{ color:{v:number | (field(lbl,"color") = 0 || colorp(field(lbt,"right"),lbr) = 0) }
                     , key:{v:A | v > field(lbl, "key")}
                     , left:{v:<l>  | ((bheightp(field(lbl,"left"),lbll) + (if (field(lbl,"color") = 0) then 1 else 0) >= 1) && (bheightp(field(lbt,"right"),lbr) = 
                                         1 + (bheightp(field(lbl,"left"),lbll) 
                                           + (if (field(lbl,"color") = 0) then 1 else 0)))) }
                     , right:{v:<r> | (bheightp(v,lbr) = 
                                       1 + (bheightp(field(lbl,"right"),lblr) + 
                                           (if (field(lbl,"color") = 0) then 1 else 0))) }
                     }
         => <x>/x |-> out:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
*/
function lbalS(t) {
  var l  = t.left;
  var r  = t.right;
  var lc = l.color;
  if (lc != 0) {
    l.color = 0;
    t.color = 1;
    return t;
  } else {
    var rc = r.color;
    if (rc == 0) {
      r.color = 1;
      t = rbal(t);
      return t;
    } else {
      var rl = r.left;
      var rr = r.right;
      if (rl != null) {
        var rlr = rl.right;
        var rlc = rl.color;
        if (rlc == 0) {
          t.right  = rl.left;
          r.left   = rl.right;
          rl.left  = t;
          rl.color = 1;
          t.color  = 0;
          assert (rr != null);
          rr.color = 1;
          r = rbal(r);
          rl.right = r;
          rl.color = 0;
          return rl;
        } else { 
          t.color = 1; 
          return t; 
        }
      } else {
        t.color = 1;
        return t;
      }
    }
  }
}
