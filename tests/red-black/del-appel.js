
/*@ include red-black.js */

/*@ qualif Foo(v:a): (( ~(Set_mem(k,keysp(v,delout))))
                     && (bheightp(v,delout) > 0)
                     && ((Prop(field(doneOut, "b")) && (colorp(x,delin) = 0)) => (colorp(v,delout) = 0))
                     && (Prop(field(doneOut, "b")) => (bheightp(x,delin) = bheightp(v,delout)))
                     && ((~(Prop(field(doneOut,"b")))) => 
                          ((colorp(x,delin) != 0) => ((bheightp(x,delin) = bheightp(v,delout)))))
                     && ((~(Prop(field(doneOut,"b")))) => 
                          ((colorp(x,delin) = 0) => (bheightp(x,delin) = 1 + bheightp(v,delout)))))      */
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

/* qualif BHeight(v:a): bheightp(v,delout) > 0     */
/* qualif SetMem(v:a): ~Set_mem(k,keysp(v,delout)) */

/*
rb_delete :: forall A <p :: (A) => prop>.
  (x:<t>+null, done:<d>, k:A)
  /t |-> delin:rbtree[A<p>]<{\x y -> x > y},{\x y -> x < y}>
  *d |-> doneIn:{ b:boolean }
     => {v:<r>+null |  (( ~(Set_mem(k,keysp(v,delout))))
                     && (bheightp(v,delout) > 0)
                     && ((Prop(field(doneOut, "b")) && (colorp(x,delin) = 0)) => (colorp(v,delout) = 0))
                     && (Prop(field(doneOut, "b")) => (bheightp(x,delin) = bheightp(v,delout)))
                     && ((~(Prop(field(doneOut,"b")))) => 
                          ((colorp(x,delin) != 0) => ((bheightp(x,delin) = bheightp(v,delout)))))
                     && ((~(Prop(field(doneOut,"b")))) => 
                          ((colorp(x,delin) = 0) => (bheightp(x,delin) = 1 + bheightp(v,delout))))) }
        /r |-> delout:rbtree[{v:A<p> | v != k}]<{\x y -> x > y},{\x y -> x < y}>
        *d |-> doneOut:{ b:boolean }
*/
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
