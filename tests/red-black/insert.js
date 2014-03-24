/*@ include red-black.js */

/*@ rotate_left :: forall K K2 L L2 R.
      (p:<z>)/z |-> zi:{ color:number, key:K,  left:L,  right:<r> }
            * r |-> ri:{ color:number, key:K2, left:L2, right:R   }
        => <r>/r |-> ro:{ color:number, key:K2, left:<z>, right:R  }
             * z |-> zo:{ color:number, key:K,  left:L,   right:L2 } */
function rotate_left(p) {
  var pr   = p.right;
  var prl  = pr.left;
  p.right  = prl;
  pr.left  = p;
  pr.color = 0;
  p.color  = 1;
  return pr;
}

/*@ rotate_right :: forall K K2 L R R2.
     (p:<t>)/t |-> it:{ color:number, key:K, left:<l>, right:R  } 
           * l |-> il:{ color:number, key:K2, left:L, right:R2 } 
        => <l>/l |-> ol:{ color:number, key:K2, left:L, right:<t>} 
             * t |-> ot:{ color:number, key:K, left:R2, right:R }*/
function rotate_right(p) {
  var pl  = p.left;
  var plr = pl.right;
  p.left = plr;
  pl.right = p;
  pl.color = 0;
  p.color  = 1;
  return pl;
}

/* qualif DooHickey(v:a,x:b): v < field(x,"key") */
/* qualif DooHickey(v:a,x:b): v > field(x,"key") */

/*@ qualif IsRed(v:a): (((Prop v) <=> (colorp(x,in) != 0))
                      && (colorp(x,out) = colorp(x,in))
                      && (bheightp(x,out) = bheightp(x,in))) */

/*@ is_red :: forall A.
                (x:<t>+null)/t |-> in:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>
                  => boolean/t |-> out:rbtree[A]<{\x y -> x > y},{\x y -> x < y}>  */
function is_red(x) {
  if (x == null) {
    return false;
  } else {
    var xc = x.color; 
    return (xc != 0);
  }
}

 /*@
   insert :: forall A.
     (p:<t>+null, k:A)/t |-> in:rbtree[A]<{\h v -> v < h},{\h v -> v > h}>
          => {v:<u>+null | v != null}
             / a |-> lft:rbtree[{v:A | v < field_int(out,"key")}]<{\h v -> v < h},{\h v -> v > h}>
             * b |-> rgt:rbtree[{v:A | v > field_int(out,"key")}]<{\h v -> v < h},{\h v -> v > h}>
             * u |-> out:{ color : { v:number | (((v != 0) => (bheightp(p,in) =     bheightp(field_Ref(out,"left"),lft))) &&
                                                 ((v != 0) => (bheightp(p,in) =     bheightp(field_Ref(out,"right"),rgt))) &&
                                                 ((v = 0)  => (bheightp(p,in) = 1 + bheightp(field_Ref(out,"left"),lft))) &&
                                                 ((v = 0)  => (bheightp(p,in) = 1 + bheightp(field_Ref(out,"right"),rgt))) &&
                                                 ((v = 0) || (((colorp(field_Ref(out,"left"),lft) = 0) || (colorp(field_Ref(out,"right"),rgt) = 0)) 
                                                           && ((colorp(p,in) != 0) || ((colorp(field_Ref(out,"left"),lft) = 0) && (colorp(field_Ref(out,"right"),rgt) = 0))))))
                                                }
                         , key:   A
                         , left:  {v:<a>+null  | (v = v && bheightp(v,lft) = bheightp(field_Ref(out,"right"),rgt)) }
                         , right: {v:<b>+null  | (v = v && bheightp(v,rgt) = bheightp(field_Ref(out,"left"),lft))  }
                         }

*/
function insert (p,k) {
  if (p == null) {
    var y = {};
    y.color = 1;
    y.key = k;
    y.left = null;
    y.right = null;
    return y;
  } 

  var pk = p.key;
  if (pk == k) {
    var pl = p.left;
    return p;
  } else {
    if (k < pk) {
      p.left = insert(p.left, k);
      var pl  = p.left;
      var plc = pl.color;
      if (plc != 0) { // RED
        var pr = p.right;
        if (is_red(pr)) {
          pl.color = 0; 
          pr.color = 0; 
          p.color  = 1;
          return p;
        } else {
          var pll = pl.left;
          if (is_red(pll)) {
            var p = rotate_right(p);
            return p;
          } else {
            var plr = pl.right;
            if (is_red(plr)) {
              plr.color = 0;
              p.left = rotate_left(pl);
              var p = rotate_right(p);
              return p; 
            }  else {
              return p;
            }
          }
        }
      } else {
        return p;
      }
    } else {
      p.right = insert(p.right, k);
      var pr  = p.right;
      var prc = pr.color;
      if (prc != 0) { // RED
        var pl = p.left;
        if (is_red(pl)) {
          pr.color = 0; 
          pl.color = 0; 
          p.color  = 1;
          return p;
        } else {
          var prr = pr.right;
          if (is_red(prr)) {
            var p = rotate_left(p);
            return p;
          } else {
            var prl = pr.left;
            if (is_red(prl)) {
              prl.color = 0;
              p.right = rotate_right(pr);
              var p = rotate_left(p);
              return p; 
            }  else {
              return p;
            }
          }
        }
      } else {
        return p;
      }
    }
  }
}
