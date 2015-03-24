
/*@ include red-black.js */

/*@ qualif PApp(v:a): (papp1 p v) */

/*@ qualif Foo(v:a,z:b): (( ~(Set_mem(k,keysp(v,z))))
                     && (bheightp(v,z) > 0)
                     && ((Prop(field(doneOut, "b")) && (colorp(x,delin) = 0)) => (colorp(v,z) = 0))
                     && (Prop(field(doneOut, "b")) => (bheightp(x,delin) = bheightp(v,z)))
                     && ((~(Prop(field(doneOut,"b")))) => 
                          ((colorp(x,delin) != 0) => ((bheightp(x,delin) = bheightp(v,z)))))
                     && ((~(Prop(field(doneOut,"b")))) => 
                          ((colorp(x,delin) = 0) => (bheightp(x,delin) = 1 + bheightp(v,z)))))      */
/*@ is_black :: forall A.
                (x:<t>+null)/t |-> tin:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
                  => {b:boolean | (((Prop b) <=> (colorp(x,tout) = 0 && x != null))
                                    && (colorp(x,tout) = colorp(x,tin))
                                    && (bheightp(x,tout) = bheightp(x,tin)))}
                      /t |-> tout:{v:rbtree[A]<{\x y -> x > y},{\x y -> x < y}> | keys(v) = keys(tin)} */

/*@ is_red :: forall A.
                (x:<t>+null)/t |-> tin:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
                  => {b:boolean | (((Prop b) <=> (colorp(x,tout) != 0))
                                    && (colorp(x,tout) = colorp(x,tin))
                                    && (bheightp(x,tout) = bheightp(x,tin)))}
                      /t |-> tout:{v:rbtree[A]<{\x y -> x > y},{\x y -> x < y}> | keys(v) = keys(tin)} */

/*@ append :: forall A <p :: (A) => prop>.
      (l:{v:<l>+null | bheightp(v,inl) = bheightp(r,inr)}, k:A, r:{v:<r>+null | bheightp(v,inr) = bheightp(l,inl)})
      /l |-> inl:rbtree[{v:A<p> | v < k}]<{\h v -> h > v},{\h v -> h < v}>
     * r |-> inr:rbtree[{v:A<p> | v > k}]<{\h v -> h > v},{\h v -> h < v}>
        => <p>/t |-> outt:rbtree[A<p>]<{\h v -> h > v},{\h v -> h < v}>                            
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
/*@
  rbalS :: forall A <p :: (A) => prop>.
    (t:{v:<t> | true})/
            r  |-> lbr:rbtree[{v:A<p> | v > field(lbt, "key")}]<{\x y -> x > y},{\x y -> x < y}>
          * l  |-> lbl:rbtree[{v:A<p> | v < field(lbt, "key")}]<{\x y -> x > y},{\x y -> x < y}> 
          * t  |-> lbt:{ color:number
                       , key:A<p>
                       , left:{v:<l>       | ((bheightp(v,lbl) = (1 + bheightp(field(lbt,"right"),lbr)))
                                           && (bheightp(v,lbl) > 1))                                  }
                       , right:{v:<r>+null | ((bheightp(v,lbr) + 1) = bheightp(field(lbt,"left"),lbl)) }
                       }
         => {v:<x> | ((if (colorp(field(lbt,"right"),lbr) != 0) then
                         (if (colorp(field(lbt,"left"),lbl) != 0) then
                            ((bheightp(v,out) = bheightp(field(lbt,"left"),lbl) + 1) && (colorp(v,out) = 0))
                         else
                            ((bheightp(v,out) = bheightp(field(lbt,"left"),lbl)) && (colorp(v,out) != 0)))
                     else (if (colorp(field(lbt,"left"),lbl) != 0) then
                        ((bheightp(v,out) = bheightp(field(lbt,"left"),lbl) + 1) && (colorp(v,out) = 0))
                     else
                        (((bheightp(v,out) = bheightp(field(lbt,"left"),lbl))))))

                     && (keysp(v,out) = keysp(field(lbt,"left"),lbl) ∪ keysp(field(lbt,"right"),lbr) ∪1 field(lbt,"key")))
                        }
            /x |-> out:rbtree[A<p>]<{\x y -> x > y},{\x y -> x < y}>
*/

/*@ lemma_nonMem :: forall A <p :: (A) => prop>. 
     (k:A, q:<q>+null)/q |-> nmin:rbtree[{v:A<p> | v != k}]<{\x y -> x > y},{\x y -> x < y}>
       => {v:number | ((~(Set_mem(k,keysp(q,nmout))))
                      && (keysp(q,nmin) = keysp(q,nmout))
                      && (bheightp(q,nmin) = bheightp(q,nmout))
                      && (colorp(q,nmin) = colorp(q,nmout)))}
          /q |-> nmout:rbtree[{v:A<p> | v != k}]<{\x y -> x > y},{\x y -> x < y}> */
function lemma_nonMem(k,q) {
  if (q == null) {
    return 0;
  } else {
    var qk = q.key;
    var l = q.left;
    var r = q.right;
    lemma_nonMem(k,l);
    lemma_nonMem(k,r);
    return 0;
  }
}
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
         => {v:<x> | ((((field(bl,"color") != 0) 
                      && (keysp(v,out) = 
                           (keysp(field(bl,"left"),bll) ∪ keysp(field(bl,"right"),blr) ∪ keysp(field(bt,"right"),br) ∪1 field(bt,"key") ∪1 field(bl,"key")))
                      && (field(bt, "left") != null) 
                      && ((colorp(field(bl,"left"),bll) != 0 || colorp(field(bl,"right"),blr) != 0))) <=> 
                        (colorp(v,out) != 0)) && (bheightp(v,out) = 1 + bheightp(field(bt, "right"), br)))}
            /x |-> out:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
*/

/*@
  lbalS :: forall A <p :: (A) => prop>.
    (t:{v:<t> | true})/
            r  |-> lbr:rbtree[{v:A<p> | v > field(lbt, "key")}]<{\x y -> x > y},{\x y -> x < y}>
          * l  |-> lbl:rbtree[{v:A<p> | v < field(lbt, "key")}]<{\x y -> x > y},{\x y -> x < y}> 
          * t  |-> lbt:{ color:number
                       , key:A<p>
                       , left:{v:<l>+null  | (bheightp(v,lbl) + 1 = bheightp(field(lbt,"right"),lbr)) }
                       , right:{v:<r> | ((bheightp(v,lbr) = bheightp(field(lbt,"left"),lbl) + 1)
                                       && (bheightp(v,lbr) > 1)) }
                       }
         => {v:<x> | ((if (colorp(field(lbt,"left"),lbl) != 0) then
                         (if (colorp(field(lbt,"right"),lbr) != 0) then
                            ((bheightp(v,out) = bheightp(field(lbt,"right"),lbr) + 1) && (colorp(v,out) = 0))
                         else
                            ((bheightp(v,out) = bheightp(field(lbt,"right"),lbr)) && (colorp(v,out) != 0)))
                     else (if (colorp(field(lbt,"right"),lbr) != 0) then
                        ((bheightp(v,out) = bheightp(field(lbt,"right"),lbr) + 1) && (colorp(v,out) = 0))
                     else
                        (((bheightp(v,out) = bheightp(field(lbt,"right"),lbr))))))

                     && (keysp(v,out) = keysp(field(lbt,"left"),lbl) ∪ keysp(field(lbt,"right"),lbr) ∪1 field(lbt,"key")))
                        }
            /x |-> out:rbtree[A<p>]<{\x y -> x > y},{\x y -> x < y}>
*/
// function lbalS(t) 
// {
//   var l = t.left;
//   var r = t.right;
//   if (is_red(l)) {
//     if (is_red(r)) {
//       l.color = 0;
//       t.color = 0;
//       return t;
//     } else {
//       t.color = 1;
//       l.color = 0;
//       return t;
//     }
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

/*@
rb_delete :: forall A.
  (x:<t>+null, done:<d>, k:A)/t |-> delin:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
                            * d |-> doneIn:{ b:boolean }
     => <r>+null/r |-> delout:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
               * d |-> doneOut:{ b:boolean }
*/
// function rb_delete(x,done,k)
// {
//   if (x == null) {
//     done.b = true;
//     return null;
//   }

//   var tc = x.color;
//   var tk = x.key;
//   var tl = x.left;
//   var tr = x.right;
  
//   if (k == tk) {
//     var d = append(tl, k, tr);
//     t = d.tree;
//     g = d.grew;
//     done.b = g;
//     lemma_nonMem(k, t);
//     return t;
//   } else {
//     if (k < tk) {
//       if (is_black(tl)) {
//         x.left = rb_delete(tl,done,k);
//         var b  = done.b;
//         if (b) { 
//           lemma_nonMem(k, x);
//           return x; 
//         } else {
//           done.b = is_red(tr);
//           x      = lbalS(x);
//           lemma_nonMem(k, x);
//           return x;
//         }
//       } else { 
//         x.left = rb_delete(tl,done,k);
//         lemma_nonMem(k,x);
//         done.b = true;
//         return x;
//       }
//     } else {
//       if (is_black(tr)) {
//         x.right = rb_delete(tr,done,k);
//         var b = done.b;
//         if (b) {
//           lemma_nonMem(k,x);
//           return x;
//         } else {
//           done.b = is_red(tl);
//           x      = rbalS(x);
//           lemma_nonMem(k, x);
//           return x;
//         }
//       } else {
//         x.right = rb_delete(tr,done,k);
//         lemma_nonMem(k,x);
//         done.b = true;
//         return x;
//       }
//     }
//   }
// }

// /*@ 
//   remove :: forall A.
//     (k:A, t:<t>+null)/t |-> in:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
//       => {v:<u>+null | (~(Set_mem(k,keysp(v,out))))}
//          /u |-> out:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>    */
// function remove(k,t) {
//   done = { b:false };
//   t = rb_delete(t,done,k);
//   return t;
// }
