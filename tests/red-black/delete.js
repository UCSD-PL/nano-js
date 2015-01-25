
/*@ include red-black.js */

/*@ lemma_nonMem :: forall A B.
     (k:A, x:<q>+null)/q |-> in:rbtree[B]<{\x y -> x > y},{\x y -> x < y}>
       => number/q |-> out:rbtree[B]<{\x y -> x > y},{\x y -> x < y}> */
function lemma_nonMem(k,x) {
  if (x == null) {
    return 0;
  } else {
    var xk = x.key;
    var l = x.left;
    var r = x.right;
    lemma_nonMem(k,l);
    lemma_nonMem(k,r);
    return 0;
  }
}

/*@ qualif Nomem(v:T,k:a): (~(Set_mem(k,keys(v)))) */ 
/*@ qualif IsRed(v:boolean, x:T): ((Prop v) <=> (col(x) != 0)) */
/*@ qualif IsB(v:boolean, x:T): ((Prop v) <=> (col(x) = 0 && (~(Prop(nil(x)))))) */

/*@ qualif Presv(v:T,x:T): (keys(v) = keys(x)) */
/*@ qualif Presv(v:T,x:T): (col(v) = col(x)) */
/*@ qualif Presv(v:T,x:T): (bheight(v) = bheight(x)) */

/* qualif Delete(v:T,x:T,y:Rec): ((Prop(field_int(y, "b")) && (col(x) = 0)) => (col(v) = 0))                           */ 
/* qualif Delete(v:T,x:T,y:Rec): (Prop(field_int(y, "b")) => (bheight(x) = bheight(v)))                                    */
/* qualif Delete(v:T,x:T,y:Rec): ((~(Prop(field_int(y,"b")))) => ((col(x) != 0) => ((bheight(x) = bheight(v)))))  */
/* qualif Delete(v:T,x:T,y:Rec): ((~(Prop(field_int(y,"b")))) => ((col(x) = 0) => (bheight(x) = 1 + bheight(v)))) */
/* qualif AppendTree(v:T,rpair:Rec,l:T):(bheight(v) = bheight(l) + (if (~(Prop(field_int(rpair,"grew")))) then 0 else 1)) */
/* qualif AppendTree(v:Ref, l:Ref, r:Ref): ((Prop(nil(v))) <=> (Prop(nil(l)) && Prop(nil(r)))) */
/* qualif AppendHeight(v:T, x:T): bheight(v) = bheight(x) */
/* qualif AppendGrew(v:boolean,x:T,l:T,r:T):((((col(x) != 0)
                                               || (col(l) = 0 && col(r) = 0)) => (~(Prop(v)))) 
                                               && ((~Prop(nil(l)) && (~(Prop(nil(r)))) && ((col(l) != 0) || (col(r) != 0))) => (Prop(v)))) */

// CAN WE AUTOGEN THESE??????
/*@ qualif Foo(v:a, x:Rec): (v > field_int(x,"key")) */
/*@ qualif Foo(v:a, x:Rec): (v < field_int(x,"key")) */
/*@ qualif Left(v:Ref, r:Rec): v = field_Ref(r, "left") */
/*@ qualif Right(v:Ref, r:Rec): v = field_Ref(r, "right") */
/*@ qualif RBalRet(v:Rec) : (~(Prop(nil(field_Ref(v,"left"))))) */
/*@ qualif RBalRet(v:Rec) : (~(Prop(nil(field_Ref(v,"right"))))) */
/*@ qualif RBalCol(v:Rec) : field_Ref(v,"color") != 0 */
/*@ qualif RBalCol(v:Rec) : field_Ref(v,"color") = 0 */

/* qualif HeightEqT(v:Ref, br:T, bl:T): bheight(br) = 
    (if (Prop(nil(br))) then 1 else (bheight(bll) 
  + (if (field_int(bl,"color") = 0) then 1 else 0))) */
//29
/* qualif HeightEqT(v:Ref): (bheight(bl) = (if (v = null) then 1 else
     (bheight(brl) + (if (field_int(br,"color") = 0) then 1 else 0)))) */
//29
/* qualif HeightEqT(v:Ref, w:Rec, x:bl, y:br, z:brl): (bheightp(field_Ref(w, [ "left" ; "right" ]), x) = (if (v = null) then 1 else
     (bheightp(field_Ref(y, ["left ; "right"]), z) + (if (field_int(y, "color") = 0) then 1 else 0)))) */
//37


/* qualif HeightEqT(v:T): bheight(v) = (if (field_Ref(bt,"left") = null) then 1 else
                                                (bheight(blr) 
                                                     + (if (field_int(bl,"color") = 0) then 1 else 0))) */
//25
/* qualif HeightEqT(v:T): (bheight(v) = (if (field_Ref(bt,"right") = null) then 1 else
                                                ((bheight(brr) 
                                                      + (if (field_int(br,"color") = 0) then 1 else 0))))) */
//25


/*@ qualif Thing(v:T, bll:T, blr:T, br:T): (((keys(v) = 
                           (keys(blr) ∪ keys(bll) ∪ keys(br) ∪1 field_int(bt,"key") ∪1 field_int(bl,"key"))
                      && ((col(blr) != 0 || col(bll) != 0))) <=> 
                        (col(v) != 0)) && (bheight(v) = 1 + bheight(br))) */
//60
/* qualif RbalRet(v:T, brl:T, brr:T, bl:T):
                      (((keys(v) = 
                           (keys(brl) ∪ keys(brr) ∪ keys(bl) ∪1 field_int(bt,"key") ∪1 field_int(br,"key"))
                      && ((col(brl) != 0 || col(brr) != 0))) <=> 
                        (col(v) != 0)) && (bheight(v) = 1 + bheight(bl))) */
//60
/*@ qualif RbalS(v:T,rbr:T): (bheight(v) = bheight(rbr) + 1) */
//10
/* qualif LbalS(v:T): (bheight(v) = bheight(lbl) + 1) */

/*@ qualif BalS1(v:T,rbl:T) :  (bheight(v) = bheight(rbl) + (if (col(rbl) != 0) then 1 else 0))      */

/*@ qualif BalS2(v:T,x:T) :  ((col(v) != 0) => (col(x) = 0)) */
/*@ qualif BalS4(v:T,x:T) :  ((col(v) = 0) => (col(x) != 0)) */

/*@ qualif BalS(v:T, x:T): (bheight(v) + 1 = bheight(x))       */
/* qualif HGt1(v:T): bheight(v) > 1 */

/*@ qualif Singl(v:Ref,x:T) : (Prop(nil(v)) => Prop(nil(x))) */
/*@ qualif Singl(v:Ref,x:Ref) : (Prop(nil(v)) <=> Prop(nil(x))) */


/*@ is_black :: forall A.
                (x:<t>+null)/t |-> isin:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
                  => b:boolean/t |-> isout:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>  */
// function is_black(x) 
// {
//   if (x == null) 
//   {
//     return false;
//   } 
//   else 
//   {
//     var xc = x.color; 
//     return (xc == 0);
//   }
// }

/*@ is_red :: forall A.
                (x:{v:<t>+null | ((Prop(nil(v))) <=> (Prop(nil(inr))))})/t |-> inr:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
                  => {v:boolean | ((Prop v) <=> ((~Prop(nil(inr))) && (col(inr) != 0)))}/t |-> outr:{v:rbtree[A]<{\x y -> x > y},{\x y -> x < y}> | (((Prop(nil(v))) <=> (Prop(nil(x)))) && (bheight(v) = bheight(inr)) && (col(v) = col(inr)))}*/
/* is_red :: forall A.
                (x:<t>+null)/t |-> inr:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
                  => boolean/t |-> outr:rbtree[A]<{\x y -> x > y},{\x y -> x < y}> */
// function is_red(x) 
// {
//   if (x == null) 
//   {
//     return false;
//   } 
//   else 
//   {
//     var xc = x.color; 
//     return (xc != 0);
//   }
// }

// DONT KNOW THING IS NULL AFTER FOLDING??????

/*@
  lbal :: forall A.
    (t:<t>)/
            lr |-> blr:{v:rbtree[{v:A | ((v < field_int(bt,"key")) && (v > field_int(bl,"key")))}]<{\x y -> x > y},{\x y -> x < y}> | (bheight(v) = bheight(bll))}
          * ll |-> bll:{v:rbtree[{v:A | ((v < field_int(bt,"key")) && (v < field_int(bl,"key")))}]<{\x y -> x > y},{\x y -> x < y}> | (bheight(v) = bheight(blr))}
          * r  |-> br:rbtree[{v:A | ((v > field_int(bt,"key")))}]<{\x y -> x > y},{\x y -> x < y}> 
          * l  |-> bl:{ color:number, key:{v:A | (v < field_int(bt,"key"))}, left:{v:<ll>+null | (Prop(nil(v)) <=> Prop(nil(bll)))}, right:{v:<lr>+null | (Prop(nil(v)) <=> Prop(nil(blr))) }}
          * t  |-> bt:{ color:number, key:A, left:{v:<l>+null | ((bheight(br) = (if (v = null) then 1 else ((if (field_int(bl,"color") = 0) then 1 else 0) + bheight(bll)))) && (Prop(nil(v)) <=> Prop(nil(bl))))}, right:{v:<r>+null | (Prop(nil(v)) <=> Prop(nil(br)))}}
         => <x>/x |-> lbalout:{v:rbtree[A]<{\x y -> x > y},{\x y -> x < y}> | ((((field_int(bl,"color") != 0) 
                      && (field_Ref(bt, "left") != null) 
                      && ((col(bll) != 0 || col(blr) != 0))) <=> 
                        (col(lbalout) != 0)) && (bheight(lbalout) = 1 + bheight(br)))}
*/
// function lbal(t)  
// {
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

         // => <x>/x |-> lbalout:{v:rbtree[A]<{\x y -> x > y},{\x y -> x < y}> | ((((field_int(bl,"color") != 0) 
         //              && (field_Ref(bt, "left") != null) 
         //              && ((col(bll) != 0 || col(blr) != 0))) <=> 
         //                (col(lbalout) != 0)) && (bheight(lbalout) = 1 + bheight(br)))}
/*@
  rbal :: forall A.
    (t:<t>)/rr |-> brr:{v:rbtree[{v:A | ((v > field_int(bt,"key")) && (v > field_int(br,"key")))}]<{\x y -> x > y},{\x y -> x < y}> | (bheight(v) = bheight(brl))}
          * rl |-> brl:rbtree[{v:A | ((v > field_int(bt,"key")) && (v < field_int(br,"key")))}]<{\x y -> x > y},{\x y -> x < y}>
          * l  |-> bl:rbtree[{v:A | ((v < field_int(bt,"key")))}]<{\x y -> x > y},{\x y -> x < y}>
          * r  |-> br:{ color:number, key:{v:A | v > field_int(bt,"key")}, left:{v:<rl>+null | (Prop(nil(v)) <=> Prop(nil(brl))) }, right:{v:<rr>+null |(Prop(nil(v)) <=> Prop(nil(brr))) } }
          * t  |-> bt:{ color:number, key:A, left:{v:<l>+null | (Prop(nil(v)) <=> Prop(nil(bl)))}, right:{v:<r>+null | ((bheight(bl) = (if (v = null) then 1 else ((if (field_int(br,"color") = 0) then 1 else 0) + bheight(brl)))) && (Prop(nil(v)) <=> Prop(nil(br))))} }
      => <x>/x |-> foo:{v:rbtree[A]<{\x y -> x > y},{\x y -> x < y}> | ((((field_int(br,"color") != 0) && (field_Ref(bt,"right") != null) && ((col(brr) != 0 || col(brl) != 0))) <=> (col(v) != 0)) && (bheight(v) = 1 + bheight(bl)))}

*/
// function rbal(t) 
// {
//   var tc = t.color;
//   var l  = t.left;
//   var r  = t.right;
//   if (r != null) {
//     var rc = r.color;
//     if (rc != 0) {
//       var rl = r.left;
//       var rr = r.right;
//       if (is_red(rr)) {
//         t.right  = r.left;
//         r.left  = t;
//         t.color  = 0;
//         rr.color = 0;
//         r.color  = 1;
//         return r;
//       } else {
//         if (is_red(rl)) {
//           r.left = rl.right;
//           rl.right = r;
//           t.right = rl.left;
//           rl.left = t;
//           r.color  = 0;
//           t.color  = 0;
//           rl.color = 1;
//           return rl;
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
//     t.right = null;
//     t.color = 0;
//     return t;
//   }
// }

/*@
  rbalS :: forall A.
    (t:<t>)/ r |-> rbr:rbtree[{v:A | v > field_int(rbt, "key")}]<{\x y -> x > y },{\x y -> x < y }>
           * l |-> rbl:{v:rbtree[{v:A | v < field_int(rbt, "key")}]<{\x y -> x > y },{\x y -> x < y }> | ((bheight(v) > 1) && (bheight(v) = 1 + bheight(rbr)))}
           * t |-> rbt:{ color:number, key:A, left:<l>, right:{v:<r>+null | (Prop(nil(v)) <=> Prop(nil(rbr)))} }
         => <x>/x |-> out:{v:rbtree[A]<{\x y -> x > y },{\x y -> x < y }> | (if (col(rbr) != 0) then (if (col(rbl) != 0) then (bheight(v) = bheight(rbl) + 1) else (bheight(v) = bheight(rbl))) else (if (col(rbl) != 0) then (bheight(v) = bheight(rbl) + 1) else (bheight(v) = bheight(rbl))))}
*/
// function rbalS(t) 
// {
//   var l = t.left;
//   var r = t.right;
//   if (is_red(r)) {
//     if (is_red(l)) {
//       r.color = 0;
//       t.color = 0;
//       return t;
//     } else {
//       t.color = 1;
//       r.color = 0;
//       return t;
//     }
//   } else {
//     if (is_red(l)) {
//       var lc = l.color;
//       var ll = l.left;
//       var lr = l.right;
//       t.color = 0;
//       t.left = lr.right;
//       l.right  = lr.left;
//       lr.right = t;
//       lr.left = l;
//       ll.color = 1;
//       lr.left = lbal(l);
//       return lr;
//     } else {
//       l.color = 1;
//       t = lbal(t);
//       return t;
//     }
//   }
// }

/*
  rbalS :: forall A.
    (t:<t>)/ r |-> rbr:rbtree[{v:A | v > field_int(rbt, "key")}]<{\x y -> x > y },{\x y -> x < y }>
           * l |-> rbl:{v:rbtree[{v:A | v < field_int(rbt, "key")}]<{\x y -> x > y },{\x y -> x < y }> | ((bheight(v) > 1) && (bheight(v) = 1 + bheight(rbr)))}
           * t |-> rbt:{ color:number, key:A, left:<l>, right:{v:<r>+null | (Prop(nil(v)) <=> Prop(nil(rbr)))} }
         => <x>/x |-> out:{v:rbtree[A]<{\x y -> x > y },{\x y -> x < y }> | (if (col(rbr) != 0) then (if (col(rbl) != 0) then (bheight(v) = bheight(rbl) + 1) else (bheight(v) = bheight(rbl))) else (if (col(rbl) != 0) then (bheight(v) = bheight(rbl) + 1) else (bheight(v) = bheight(rbl))))}
*/

/*@ lbalS :: forall A.
    (t:<t>)/r  |-> lbr:{v:rbtree[{v:A | v > field_int(lbt,"key")}]<{\x y -> x > y},{\x y -> x < y}> | ((bheight(v) > 1) && (bheight(v) = 1 + bheight(lbl)))}
          * l  |-> lbl:rbtree[{v:A | v < field_int(lbt,"key")}]<{\x y -> x > y},{\x y -> x < y}> 
          * t  |-> lbt:{ color:number, key:A, left:{v:<l>+null | (Prop(nil(v)) <=> Prop(nil(lbl)))}, right:<r> }
          => <x>/x |-> out:{v:rbtree[A]<{\x y -> x > y},{\x y -> x < y}> | (if (col(lbl) != 0) then (if (col(lbr) != 0) then (bheight(v) = bheight(lbr) + 1) else (bheight(v) = bheight(lbr))) else (if (col(lbr) != 0) then (bheight(v) = bheight(lbr) + 1) else (bheight(v) = bheight(lbr))))}              */
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

/*@ append :: forall A.
   (l:<l>+null, k:A, r:<r>+null)/l |-> inl:{v:rbtree[{v:A<p> | v < k}]<{\h v -> h > v },{\h v -> h < v }> | bheight(v) = bheight(inr)}
                               * r |-> inr:rbtree[{v:A<p> | v > k}]<{\h v -> h > v },{\h v -> h < v }>
     => <p>/t |-> outt:{v:rbtree[A<p>]<{\h v -> h > v},{\h v -> h < v }> | ((Prop(nil(v)) <=> (Prop(nil(l)) && Prop(nil(r)))))}
          * p |-> rpair:{ grew:{v:boolean | ((((col(outt) != 0) || (col(inl) = 0 && col(inr) = 0)) => (~(Prop(v)))) 
                                            && (if (~(Prop(v))) then (bheight(outt) = bheight(inl)) else (bheight(outt) = 1 + bheight(inr)))) } , tree:{v:<t>+null | ((Prop(nil(v)) <=> (Prop(nil(l)) && Prop(nil(r)))) && (Prop(nil(v)) <=> Prop(nil(outt))))} }           */
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

/*@ 
  remove :: forall A.
    (k:A, t:<t>+null)/t |-> y:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
      => <u>+null/u |-> z:{v:rbtree[A]<{\x y -> x > y},{\x y -> x < y}> | true }    
*/
// function remove(k,t) {
//   done = { b:false };
//   t = rb_delete(t,done,k);
//   return t;
// }
