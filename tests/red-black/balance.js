/*@ include red-black.js */

/*@ qualif IsRed(v:a): (((Prop v) <=> (colorp(x,in) != 0))
                      && (colorp(x,out) = colorp(x,in))
                      && (bheightp(x,out) = bheightp(x,in))) */

/*@ is_red :: forall A.
                (x:<t>+null)/t |-> tin:rbtree[A]<{\x y -> true},{\x y -> true}>
                  => {b:boolean | (((Prop b) <=> (colorp(x,tout) != 0))
                                    && (colorp(x,tout) = colorp(x,tin))
                                    && (bheightp(x,tout) = bheightp(x,tin)))}
                      /t |-> tout:rbtree[A]<{\x y -> true},{\x y -> true}>  */
/* is_red :: forall A.
                (x:<t>+null)/t |-> tin:rbtree[A]<{\h v -> true},{\h v -> true}>
                  => boolean/t |-> tout:rbtree[A]<{\h v -> true},{\h v -> true}>  */
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
  balance ::
    (t:{v:<t> | true})/
            lr |-> blr:rbtree[number]<{\x y -> true},{\x y -> true}>
          * ll |-> bll:rbtree[number]<{\x y -> true},{\x y -> true}>
          * rl |-> brl:rbtree[number]<{\x y -> true},{\x y -> true}>
          * rr |-> brr:rbtree[number]<{\x y -> true},{\x y -> true}>
          * r |-> br:{ color:number
                     , key:number
                     , left:<rl>+null
                     , right:{v:<rr>+null | bheightp(v,brr) = bheightp(field(br,"left"),brl)}
                     }
          * l |-> bl:{ color:number
                     , key:number
                     , left:{v:<ll>+null | (((if (field(bl,"color") = 0) then 1 else 0) + bheightp(v,bll))
                                          = ((if (field(br,"color") = 0) then 1 else 0) + bheightp(field(br,"right"),brr)))}
                     , right:{v:<lr>+null | bheightp(v,blr) = bheightp(field(bl,"left"),bll)}
                     }
          * t |-> bt:{ color:number, key:number, left:<l>, right:<r> }
         => <x>/x |-> out:rbtree[number]<{\x y -> true},{\x y -> true}>
*/
function balance(t) {
  var l = t.left;
  var r = t.right;
  
  var lc = l.color;
  var rc = r.color;
  var ll = l.left;
  var lr = l.right;
  if (lc != 0) 
  {
    if (rc != 0) 
    {
      l.color = 0;
      r.color = 0;
      t.color = 1;
      return t;
    } 
    else 
    {
      if (is_red(ll)) 
      {
        t.left   = lr;
        l.right  = t;
        r.color  = 0;
        l.color  = 1;
        ll.color = 0;
        t.color  = 0;
        return t;
      } 
      else 
      {
        if (is_red(lr)) 
        {
          l.right  = lr.left;
          t.left   = lr.right;
          lr.left  = l;
          lr.right = t;
          r.color  = 0;
          l.color  = 0;
          t.color  = 0;
          lr.color = 1;
          return lr;
        } 
        else 
        { 
          t.color = 0;
          l.color = 1;
          r.color = 0;
          return t; 
        }
      }
    }
  } 
  else 
  {
    assume(false);
    return t;
  }
}
