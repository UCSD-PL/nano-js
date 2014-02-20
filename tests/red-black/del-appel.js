
/*@ include red-black.js */

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
/*@
  lbalS :: forall A <p :: (A) => prop>.
    (t:{v:<t> | true})/
            r  |-> lbr:rbtree[{v:A<p> | v > field(lbt, "key")}]<{\x y -> x > y},{\x y -> x < y}>
          * l  |-> lbl:rbtree[{v:A<p> | v < field(lbt, "key")}]<{\x y -> x > y},{\x y -> x < y}> 
          * t  |-> lbt:{ color:number
                       , key:A
                       , left:{v:<l>+null  | ((bheightp(v,lbl) + 1 = bheightp(field(lbt,"right"),lbr))
                                       && (colorp(v,lbl) = 0 || colorp(field(lbt,"right"),lbr) = 0)) }
                       , right:{v:<r> | ((bheightp(v,lbr) = bheightp(field(lbt,"left"),lbl) + 1)
                                       && (bheightp(v,lbr) > 1)) }
                       }
         => {v:<x> | (if (colorp(field(lbt,"left"),lbl) = 1 || colorp(field(lbt,"right"),lbr) = 0) then (bheightp(v,out) = bheightp(field(lbt,"right"),lbr)) else (bheightp(v,out) = bheightp(field(lbt,"right"),lbr) + 1)) }
            /x |-> out:rbtree[A<p>]<{\x y -> x > y},{\x y -> x < y}>
*/

/*@ qualif PApp(v:a): (papp1 p v) */

/*@ lemma_nonMem :: forall A <p :: (A) => prop>. 
     (k:A, q:<q>+null)/q |-> nmin:rbtree[{v:A<p> | v != k}]<{\x y -> x > y},{\x y -> x < y}>
       => {v:number | (nmin = nmout && (~(Set_mem(k,keysp(q,nmout)))))}
          /q |-> nmout:{v:rbtree[{v:A<p> | v != k}]<{\x y -> x > y},{\x y -> x < y}> | v = nmin} */
/*@
rb_delete :: forall A <p :: (A) => prop>.
  (x:<t>+null, k:A)
  /t |-> delin:rbtree[A<p>]<{\x y -> x > y},{\x y -> x < y}>
     => {v:<r>+null | (bheightp(v,delout) = bheightp(x,delin) && (~(Set_mem(k,keysp(x,delout)))))}
        /r |-> delout:rbtree[A<p>]<{\x y -> x > y},{\x y -> x < y}>
*/
function rb_delete(x,k)
{
  if (x == null) {
    return null;
  }
  
  var tc = x.color;
  var tk = x.key;
  var tl = x.left;
  var tr = x.right;
  
  if (k < tk) {
    if (is_black(tl)) {
      assume(false);
      return x;
    } else {
      if (tl == null) {
        lemma_nonMem(k,tr);
        return x;
      } else {
        var d = rb_delete(tl, k);
        lemma_nonMem(k,tr);
        x.left = d;
        return x;
      }
    }
  } else { 
    assume(false);
    return x;
  } 
}
