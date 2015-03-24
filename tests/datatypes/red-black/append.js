/*@ include red-black.js */

/*@ is_red :: forall A.
                (x:<t>+null)/t |-> tin:rbtree[A]<{\x y -> true},{\x y -> true}>
                  => {b:boolean | (((Prop b) <=> (colorp(x,tout) != 0))
                                    && (colorp(x,tout) = colorp(x,tin))
                                    && (bheightp(x,tout) = bheightp(x,tin)))}
                      /t |-> tout:rbtree[A]<{\x y -> true},{\x y -> true}>  */
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

/*@ balance_left :: forall A.
  (t:<t>)/t |-> it:{ color:number, key:A, left:<l>+null, right:<r>+null }
        * l |-> il:rbtree[A]<{\h v -> true},{\h v -> true}
        * r |-> ir:rbtree[A]<{\h v -> true},{\h v -> true}
    => 

/*@ append :: forall A.
      (l:<l>+null, r:{v:<r>+null | bheightp(v,inr) = bheightp(l,inl)})
      /l |-> inl:rbtree[A]<{\h v -> true},{\h v -> true}>
     * r |-> inr:rbtree[A]<{\h v -> true},{\h v -> true}>
        => {v:<t>+null | (((colorp(v,outt) != 0) => (bheightp(v,outt) = bheightp(l,inl)))
                      && ((colorp(l,inl) = 0 && colorp(r,inr) = 0 &&
                          (colorp(v,outt) = 0)) => (bheightp(v,outt) = bheightp(l,inl)))
                      && (r = null => bheightp(v,outt) = bheightp(l,inl))
                      && (l = null => bheightp(v,outt) = bheightp(r,inr))
                      && ((v = null) <=> (l = null && r = null)))}
           /t |-> outt:rbtree[A]<{\h v -> true},{\h v -> true}>                            */
function append(l,r)
{
  if (l == null)
    return r;

  if (r == null)
    return l;

  if (is_red(r)) {
    if (is_red(l)) {
      var lr = l.right;
      var rl = r.left;
      var t = append(lr, rl);
      if (is_red(t)) {
        l.right = t.left;
        r.left  = t.right;
        t.left  = l;
        t.right = r;
        t.color = 0;
        return t;
      } else {
        r.left = t;
        l.right = r;
        l.color = 0;
        return l;
      }
    } else {
      var rl  = r.left;
      var t   = append(l, rl);
      r.left  = t;
      r.color = 0;
      return r;
    }
  } else {
    if (is_red(l)) {
      var lr = l.right;
      var t  = append(lr, r);
      l.right = t;
      l.color = 0;
      return l;
    } else {
      var lr = l.right;
      var rl = r.left;
      var t =  append(lr, rl);
      if (is_red(t)) {
        l.right = t.left;
        r.left  = t.right;
        t.left  = l;
        t.right = r;
        t.color = 1;
        return t;
      } else {
        l.right = r;
        r.left  = t;
        r.color = 0;
        var ret = balance_left(l);
        return ret;
      }
    }
  }
}
