
/*@ include red-black.js */

/*@ qualif PApp(v:a): (papp1 p v) */

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

/*@ is_black :: forall A.
                (x:<t>+null)/t |-> tin:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
                  => {b:boolean | (((Prop b) <=> (colorp(x,tout) = 0 && x != null))
                  
                                    && (keysp(x,tout) = keysp(x,tin))
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
                                    && (keysp(x,tout) = keysp(x,tin))
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

/*@
  lbal :: forall A.
    (t:<t>)/
            lr |-> blr:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
          * ll |-> bll:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
          * r  |-> br:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
          * l  |-> bl:{ color:number, key:A, left:<ll>+null, right:<lr>+null }
          * t  |-> bt:{ color:number, key:A, left:<l>+null, right:<r>+null}
         => v:<x>/x |-> out:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
*/
function lbal(t)  {
  var tc = t.color;
  var l  = t.left;
  var r  = t.right;
  if (l != null) {
    var lc = l.color;
    if (lc != 0) {
      var ll = l.left;
      var lr = l.right;
      if (is_red(ll)) {
        t.left   = l.right;
        l.right  = t;
        t.color  = 0;
        ll.color = 0;
        l.color  = 1;
        return l;
      } else {
        if (is_red(lr)) {
          l.right = lr.left;
          lr.left = l;
          t.left = lr.right;
          lr.right = t;
          l.color  = 0;
          t.color  = 0;
          lr.color = 1;
          return lr;
        } else {
          t.color = 0;
          return t;
        }
      }
    } else {
      t.color = 0;
      return t;
    }
  } else {
    t.left = null;
    t.color = 0;
    return t;
  }
}
/*@ qualif Foo(v:a, x:Rec): (v > field_int(x,"key")) */
/*@ qualif Foo(v:a, x:Rec): (v < field_int(x,"key")) */
/*@ qualif Left(v:Ref, r:Rec): v = field_Ref(r, "left") */
/*@ qualif Right(v:Ref, r:Rec): v = field_Ref(r, "right") */
/*@ qualif Color(v:Ref, r:Rec): v = field_Ref(r, "color") */
/*@ qualif HeightEq(v:Ref,p:Ref,bll:T,brr:T): bheightp(v,bll) = bheightp(p,blr) */

/*@ qualif HeightEqT(v:Ref): bheightp(field_Ref(bt,"right"),br) = (if (v = null) then 1 else (bheightp(field_Ref(bl,"left"),bll) + (if (field_int(bl,"color") = 0) then 1 else 0))) */

/*@ qualif HeightEqT(v:Ref): bheightp(v,br) = (if (field_Ref(bt,"left") = null) then 1 else (bheightp(field_Ref(bl,"right"),blr) + (if (field_int(bl,"color") = 0) then 1 else 0))) */

/*@ qualif Thing(v:Ref): ((((field_int(bl,"color") != 0) && (field_Ref(bt, "left") != null))
                      && (keysp(v,out) = 
                           (keysp(field_Ref(bl,"right"),blr) ∪ keysp(field_Ref(bl,"left"),bll) ∪ keysp(field_Ref(bt,"right"),br) ∪1 field_int(bt,"key") ∪1 field_int(bl,"key"))
                      && ((colorp(field_Ref(bl,"right"),blr) != 0 || colorp(field_Ref(bl,"left"),bll) != 0))) <=> 
                        (colorp(v,out) != 0)) && (bheightp(v,out) = 1 + bheightp(field_Ref(bt, "right"), br)))
*/

/*@ qualif HeightEqT(v:Ref): (bheightp(v,bl) = (if (field_Ref(bt,"right") = null) then 1 else (
                     (bheightp(field_Ref(br,"right"),brr) + (if (field_int(br,"color") = 0) then 1 else 0))))) */

/*@ qualif HeightEqT(v:Ref):
(bheightp(field_Ref(bt,"left"),bl) = (if (v = null) then 1 else (bheightp(field_Ref(br,"left"),brl) + (if (field_int(br,"color") = 0) then 1 else 0))))
*/

/*@  qualif RbalRet(v:Ref):
((((field_int(br,"color") != 0) && (field_Ref(bt,"right") != null))
                      && (keysp(v,out) = 
                           (keysp(field_Ref(br,"left"),brl) ∪ keysp(field_Ref(br,"right"),brr) ∪ keysp(field_Ref(bt,"left"),bl) ∪1 field_int(bt,"key") ∪1 field_int(br,"key"))
                      && ((colorp(field_Ref(br,"left"),brl) != 0 || colorp(field_Ref(br,"right"),brr) != 0))) <=> 
                        (colorp(v,out) != 0)) && (bheightp(v,out) = 1 + bheightp(field_Ref(bt, "left"), bl))) */
/*@
  rbal :: forall A.
    (t:<t>)/rr |-> brr:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
          * rl |-> brl:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
          * l  |-> bl: rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
          * r  |-> br:{ color:number, key:A, left:<rl>+null, right:<rr>+null }
          * t  |-> bt:{ color:number, key:A, left:<l>+null, right:<r>+null }
      => <x>/x |-> out:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>

*/
function rbal(t) {
  var tc = t.color;
  var l  = t.left;
  var r  = t.right;
  if (r != null) {
    var rc = r.color;
    if (rc != 0) {
      var rl = r.left;
      var rr = r.right;
      if (is_red(rr)) {
        t.right  = r.left;
        r.left  = t;
        t.color  = 0;
        rr.color = 0;
        r.color  = 1;
        return r;
      } else {
        if (is_red(rl)) {
          r.left = rl.right;
          rl.right = r;
          t.right = rl.left;
          rl.left = t;
          r.color  = 0;
          t.color  = 0;
          rl.color = 1;
          return rl;
        } else {
          t.color = 0;
          return t;
        }
      }
    } else {
      t.color = 0;
      return t;
    }
  } else {
    t.right = null;
    t.color = 0;
    return t;
  }
}

/*@ qualif LbalS(v:a):(if (colorp(field_Ref(lbt,"left"),lbl) != 0) then
                         (if (colorp(field_Ref(lbt,"right"),lbr) != 0) then
                            ((bheightp(v,out) = bheightp(field_Ref(lbt,"right"),lbr) + 1) && (colorp(v,out) = 0))
                         else
                            ((bheightp(v,out) = bheightp(field_Ref(lbt,"right"),lbr)) && (colorp(v,out) != 0)))
                     else (if (colorp(field_Ref(lbt,"right"),lbr) != 0) then
                        ((bheightp(v,out) = bheightp(field_Ref(lbt,"right"),lbr) + 1) && (colorp(v,out) = 0))
                     else
                        (((bheightp(v,out) = bheightp(field_Ref(lbt,"right"),lbr)))))) */
/*@ qualif LbalS(v:Ref): ((bheightp(v,lbr) = bheightp(field_Ref(lbt,"left"),lbl) + 1)
                                       && (bheightp(v,lbr) > 1))                   */
/*@ qualif LbalS(v:Ref, lbl:T, lbr:T): (bheightp(v,lbl) + 1 = bheightp(p,lbr))    */

/*@ qualif RbalS(v:Ref):(if (colorp(field_Ref(rbt,"right"),rbr) != 0) then
                         (if (colorp(field_Ref(rbt,"left"),rbl) != 0) then
                            ((bheightp(v,out) = bheightp(field_Ref(rbt,"left"),rbl) + 1) && (colorp(v,out) = 0))
                         else
                            ((bheightp(v,out) = bheightp(field_Ref(rbt,"left"),rbl)) && (colorp(v,out) != 0)))
                     else (if (colorp(field_Ref(rbt,"left"),rbl) != 0) then
                        ((bheightp(v,out) = bheightp(field_Ref(rbt,"left"),rbl) + 1) && (colorp(v,out) = 0))
                     else
                        (((bheightp(v,out) = bheightp(field_Ref(rbt,"left"),rbl)))))) */
/*@ qualif RbalS(v:Ref): ((bheightp(v,rbl) = bheightp(field_Ref(rbt,"right"),rbr) + 1)
                                       && (bheightp(v,rbl) > 1))                   */

/*@
  rbalS :: forall A.
    (t:<t>)/ r |-> rbr:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
           * l |-> rbl:rbtree[A]<{\x y -> x > y},{\x y -> x < y}> 
           * t |-> rbt:{ color:number, key:A, left:<l>, right:<r>+null}
         => <x>/x |-> out:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
*/
function rbalS(t) 
{
  var l = t.left;
  var r = t.right;
  if (is_red(r)) {
    if (is_red(l)) {
      r.color = 0;
      t.color = 0;
      return t;
    } else {
      t.color = 1;
      r.color = 0;
      return t;
    }
  } else {
    if (is_red(l)) {
      var lc = l.color;
      var ll = l.left;
      var lr = l.right;
      t.color = 0;
      t.left = lr.right;
      l.right  = lr.left;
      lr.right = t;
      lr.left = l;
      ll.color = 1;
      lr.left = lbal(l);
      return lr;
    } else {
      l.color = 1;
      t = lbal(t);
      return t;
    }
  }
}

/*@ lbalS :: forall A.
    (t:<t>)/r  |-> lbr:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
          * l  |-> lbl:rbtree[A]<{\x y -> x > y},{\x y -> x < y}> 
          * t  |-> lbt:{ color:number, key:A, left:<l>+null, right:<r> }
         => <x>/x |-> out:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>              */
function lbalS(t) 
{
  var l = t.left;
  var r = t.right;
  if (is_red(l)) {
    if (is_red(r)) {
      l.color = 0;
      t.color = 0;
      return t;
    } else {
      t.color = 1;
      l.color = 0;
      return t;
    }
  } else {
    if (is_red(r)) {
      var rc = r.color;
      var rl = r.left;
      var rr = r.right;
      t.color = 0;
      t.right = rl.left;
      r.left  = rl.right;
      rl.left = t;
      rl.right = r;
      rr.color = 1;
      rl.right = rbal(r);
      return rl;
    } else {
      r.color = 1;
      t = rbal(t);
      return t;
    }
  }
}

/*@ qualif Delete(v:a,z:b): (~(Set_mem(k,keysp(v,z))))                                                                            */
/*@ qualif Delete(v:a,z:b): bheightp(v,z) > 0                                                                                     */
/*@ qualif Delete(v:a,z:b): ((Prop(field_int(doneOut, "b")) && (colorp(x,delin) = 0)) => (colorp(v,z) = 0))                           */ 
/*@ qualif Delete(v:a,z:b): (Prop(field_int(doneOut, "b")) => (bheightp(x,delin) = bheightp(v,z)))                                    */
/*@ qualif Delete(v:a,z:b): ((~(Prop(field_int(doneOut,"b")))) => ((colorp(x,delin) != 0) => ((bheightp(x,delin) = bheightp(v,z)))))  */
/*@ qualif Delete(v:a,z:b): ((~(Prop(field_int(doneOut,"b")))) => ((colorp(x,delin) = 0) => (bheightp(x,delin) = 1 + bheightp(v,z)))) */

/*@ qualif AppendTree(v:a):((if (~(Prop(field_int(rpair,"grew")))) then
                                                    (bheightp(v,outt) = bheightp(l,inl))
                                                  else
                                                    (bheightp(v,outt) = 1 + bheightp(l,inl)))
                                              && ((v = null) <=> (l = null && r = null))
                                              && (bheightp(v,outt) > 0)) */
/*@ qualif AppendHeight(v:a): bheightp(v,inl) = bheightp(r,inr) */
/*@ qualif AppendGrew(v:a):((((colorp(field_Ref(rpair,"tree"),outt) != 0)
                                               || (colorp(l,inl) = 0 && colorp(r,inr) = 0)) => (~(Prop(v)))) 
                                               && ((l != null && r != null && ((colorp(l,inl) != 0) || (colorp(r,inr) != 0))) => (Prop(v)))) */

/*@ append :: forall A.
   (l:<l>+null, k:A, r:<r>+null)/l |-> inl:rbtree[A]<{\h v -> true },{\h v -> true }>
                               * r |-> inr:rbtree[A]<{\h v -> true },{\h v -> true }>
     => <p>/t |-> outt:rbtree[A]<{\h v -> h > v},{\h v -> true }>                            
          * p |-> rpair:{ grew:boolean, tree:<t>+null }           */
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
function rb_delete(x,done,k)
{
  if (x == null) {
    done.b = true;
    return null;
  }

  var tc = x.color;
  var tk = x.key;
  var tl = x.left;
  var tr = x.right;
  
  if (k == tk) {
    var d = append(tl, k, tr);
    t = d.tree;
    g = d.grew;
    done.b = g;
    lemma_nonMem(k, t);
    return t;
  } else {
    if (k < tk) {
      if (is_black(tl)) {
        x.left = rb_delete(tl,done,k);
        var b  = done.b;
        if (b) { 
          lemma_nonMem(k, x);
          return x; 
        } else {
          done.b = is_red(tr);
          x      = lbalS(x);
          lemma_nonMem(k, x);
          return x;
        }
      } else { 
        x.left = rb_delete(tl,done,k);
        lemma_nonMem(k,x);
        done.b = true;
        return x;
      }
    } else {
      if (is_black(tr)) {
        x.right = rb_delete(tr,done,k);
        var b = done.b;
        if (b) {
          lemma_nonMem(k,x);
          return x;
        } else {
          done.b = is_red(tl);
          x      = rbalS(x);
          lemma_nonMem(k, x);
          return x;
        }
      } else {
        x.right = rb_delete(tr,done,k);
        lemma_nonMem(k,x);
        done.b = true;
        return x;
      }
    }
  }
}

/*@ 
  remove :: forall A.
    (k:A, t:<t>+null)/t |-> in:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
      => {v:<u>+null | (~(Set_mem(k,keysp(v,out))))}
         /u |-> out:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>    */
function remove(k,t) {
  done = { b:false };
  t = rb_delete(t,done,k);
  return t;
}
