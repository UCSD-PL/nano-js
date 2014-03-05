
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
         => {v:<x> | (((field(br,"color") != 0) 
                      && (keysp(v,out) = 
                           (keysp(field(br,"left"),brl) ∪ keysp(field(br,"right"),brr) ∪ keysp(field(bt,"left"),bl) ∪1 field(bt,"key") ∪1 field(br,"key"))
                      && ((colorp(field(br,"left"),brl) != 0 || colorp(field(br,"right"),brr) != 0))) <=> 
                        (colorp(v,out) != 0)) && (bheightp(v,out) = 1 + bheightp(field(bt, "left"), bl)))}
            /x |-> out:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>

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

/*@ qualif LbalS(v:a):(if (colorp(field(lbt,"left"),lbl) != 0) then
                         (if (colorp(field(lbt,"right"),lbr) != 0) then
                            ((bheightp(v,out) = bheightp(field(lbt,"right"),lbr) + 1) && (colorp(v,out) = 0))
                         else
                            ((bheightp(v,out) = bheightp(field(lbt,"right"),lbr)) && (colorp(v,out) != 0)))
                     else (if (colorp(field(lbt,"right"),lbr) != 0) then
                        ((bheightp(v,out) = bheightp(field(lbt,"right"),lbr) + 1) && (colorp(v,out) = 0))
                     else
                        (((bheightp(v,out) = bheightp(field(lbt,"right"),lbr)))))) */

/*@ qualif LbalS(v:a): ((bheightp(v,lbr) = bheightp(field(lbt,"left"),lbl) + 1)
                                       && (bheightp(v,lbr) > 1))                   */
/*@ qualif LbalS(v:a): (bheightp(v,lbl) + 1 = bheightp(field(lbt,"right"),lbr))    */

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

/*@ qualif Delete(v:a,z:b): (( ~(Set_mem(k,keysp(v,z))))
                     && (bheightp(v,z) > 0)
                     && ((Prop(field(doneOut, "b")) && (colorp(x,delin) = 0)) => (colorp(v,z) = 0))
                     && (Prop(field(doneOut, "b")) => (bheightp(x,delin) = bheightp(v,z)))
                     && ((~(Prop(field(doneOut,"b")))) => 
                          ((colorp(x,delin) != 0) => ((bheightp(x,delin) = bheightp(v,z)))))
                     && ((~(Prop(field(doneOut,"b")))) => 
                          ((colorp(x,delin) = 0) => (bheightp(x,delin) = 1 + bheightp(v,z)))))      */

/*@ qualif AppendTree(v:a):((if (~(Prop(field(rpair,"grew")))) then
                                                    (bheightp(v,outt) = bheightp(l,inl))
                                                  else
                                                    (bheightp(v,outt) = 1 + bheightp(l,inl)))
                                              && ((v = null) <=> (l = null && r = null))
                                              && (bheightp(v,outt) > 0)) */
/*@ qualif AppendHeight(v:a): bheightp(v,inl) = bheightp(r,inr) */
/*@ qualif AppendGrew(v:a):((((colorp(field(rpair,"tree"),outt) != 0)
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
