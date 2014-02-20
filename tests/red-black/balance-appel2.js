/*@ include red-black.js */

/*@ is_black :: forall A.
                (x:<t>+null)/t |-> tin:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
                  => {b:boolean | (((Prop b) <=> (colorp(x,tout) = 0 && x != null))
                                    && (colorp(x,tout) = colorp(x,tin))
                                    && (bheightp(x,tout) = bheightp(x,tin)))}
                      /t |-> tout:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>  */
function is_black(x) 
{
  if (x == null) 
  {
    return false;
  } 
  else 
  {
    var xc = x.color; 
    return (xc == 0);
  }
}

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
            r  |-> lbr:rbtree[{v:A | v > field(lbt, "key")}]<{\x y -> x > y},{\x y -> x < y}>
          * l  |-> lbl:rbtree[{v:A | v < field(lbt, "key")}]<{\x y -> x > y},{\x y -> x < y}> 
          * t  |-> lbt:{ color:number
                       , key:A
                       , left:{v:<l>+null  | ((bheightp(v,lbl) + 1 = bheightp(field(lbt,"right"),lbr))
                                       && (colorp(v,lbl) = 0 || colorp(field(lbt,"right"),lbr) = 0)) }
                       , right:{v:<r> | ((bheightp(v,lbr) = bheightp(field(lbt,"left"),lbl) + 1)
                                       && (bheightp(v,lbr) > 1)) }
                       }
         => {v:<x> | (if (colorp(field(lbt,"left"),lbl) = 1 || colorp(field(lbt,"right"),lbr) = 0) then (bheightp(v,out) = bheightp(field(lbt,"right"),lbr)) else (bheightp(v,out) = bheightp(field(lbt,"right"),lbr) + 1)) }
            /x |-> out:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
*/
// function lbalS(t) 
// {
//   var l = t.left;
//   var r = t.right;
//   if (is_red(l)) {
//     t.color = 1;
//     l.color = 0;
//     return t;
//   } else {
//     if (is_red(r)) {
//       var rc = r.color;
//       var rl = r.left;
//       var rr = r.right;
//       t.color = 0;
//       t.right = rl.left;
//       r.left  = rl.right;
//       rl.left = t;
//       rl.right = r;
//       rr.color = 1;
//       rl.right = rbal(r);
//       return rl;
//     } else {
//       r.color = 1;
//       t = rbal(t);
//       return t;
//     }
//   }
// }

/*@ assert_eq :: forall A. (p:<p>+null, q:{v:<q>+null | bheightp(p,pp) = bheightp(q,qq)})
                            /p |-> pp:rbtree[A]<{\h v -> h > v},{\h v -> h < v}> 
                           * q |-> qq:rbtree[A]<{\h v -> h > v},{\h v -> h < v}> 
       => void/emp */

/*@ append :: forall A.
      (l:{v:<l>+null | bheightp(v,inl) = bheightp(r,inr)}, k:A, r:{v:<r>+null | bheightp(v,inr) = bheightp(l,inl)})
      /l |-> inl:rbtree[{v:A | v < k}]<{\h v -> h > v},{\h v -> h < v}>
     * r |-> inr:rbtree[{v:A | v > k}]<{\h v -> h > v},{\h v -> h < v}>
        => <p>/t |-> outt:rbtree[A]<{\h v -> h > v},{\h v -> h < v}>                            
             * p |-> rpair: { grew:{v:boolean | (((colorp(field(rpair,"tree"),outt) != 0)
                                                 || (colorp(l,inl) = 0 && colorp(r,inr) = 0)) => (~(Prop(v))))}, 
                              tree:{v:<t>+null | ((if (~(Prop(field(rpair,"grew")))) then
                                                    (bheightp(v,outt) = bheightp(l,inl))
                                                  else
                                                    (bheightp(v,outt) = 1 + bheightp(l,inl)))
                                              && ((v = null) <=> (l = null && r = null))
                                              && (bheightp(v,outt) > 0))}
                                   }
*/
function append(l,k,r)
{
  if (l == null)
    return {grew:false, tree:r};

  if (r == null)
    return {grew:false, tree:l};

  if (is_red(r)) {
    if (is_red(l)) {
      var lk = l.key;
      var rk = r.key;
      var lr = l.right;
      var rl = r.left;
      var p = append(lr, k, rl);
      g = p.grew;
      t = p.tree;
      if (is_red(t)) {
        l.right = t.left;
        r.left  = t.right;
        t.left  = l;
        t.right = r;
        t.color = 0;
        return {grew:true, tree:t};
      } else {
        r.left = t;
        l.right = r;
        l.color = 0;
        return {grew:true, tree:l};
      }
    } else {
      var rk  = r.key;
      var rl  = r.left;
      var p   = append(l, k, rl);
      g = p.grew;
      t = p.tree;
      r.left  = t;
      r.color = 0;
      var ret = { grew:true, tree:r };
      return ret;
    }
  } else {
    if (is_red(l)) {
      var lk = l.key
      var lr = l.right;
      var p  = append(lr, k, r);
      var t = p.tree;
      var g = p.grew;
      l.right = t;
      l.color = 0;
      return {grew:true, tree:l};
    } else {
      var lk = l.key
      var rk = r.key
      var lr = l.right;
      var rl = r.left;
      var p  = append(lr, k, rl);
      var t  = p.tree;
      var g  = p.grew;
      if (is_red(t)) {
        l.right = t.left;
        r.left  = t.right;
        t.left  = l;
        t.right = r;
        t.color = 1;
        var ret = {grew:false, tree:t};
        return ret;
      } else {
        if (g) {
          l.right = t.left;
          r.left = t.right;
          t.left = l;
          t.right = r;
          t.color = 1;
          ret = {grew:false, tree:t};
          return ret;
        } else {
          l.right = r;
          r.left  = t;
          r.color = 0;
          var ret = lbalS(l);
          return {grew:false, tree:ret};
        }
      }
    }
  }
}
