/*@ include red-black.js */

/*@ rotate_left :: forall K K2 L L2 R.
      (p:<z>)/z |-> zi:{ color:number, key:K,  left:L,  right:<r> }
            * r |-> ri:{ color:number, key:K2, left:L2, right:R   }
        => <r>/r |-> ro:{ color:{v:number | v = 0}, key:K2, left:<z>, right:R  }
             * z |-> zo:{ color:{v:number | v = 1}, key:K,  left:L,   right:L2 } */
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
     (p:<t>)/t |-> { color:number, key:K, left:<l>, right:R  } 
           * l |-> { color:number, key:K2, left:L, right:R2 } 
        => <l>/l |-> { color:{v:number | v = 0}, key:K2, left:L, right:<t>} 
             * t |-> { color:{v:number | v = 1}, key:K, left:R2, right:R }*/
function rotate_right(p) {
  var pl  = p.left;
  var plr = pl.right;
  p.left = plr;
  pl.right = p;
  pl.color = 0;
  p.color  = 1;
  return pl;
}

/*@ is_red :: forall <f :: (number,number) => prop, g :: (number,number) => prop, h :: (number) => prop>. 
                (x:<t>+null)/t |-> in:rbtree[number<h>]<f,g> 
                  => {b:boolean | ((Prop b) <=> (colorp(x,in) != 0))}
                     /t |-> out:{v:rbtree[number<h>]<f,g> | v = in}                  */

/*@ qualif QApp(v:a): (papp1 q v) */
/*@ qualif GTField(v:a,x:a): (v > field(x, "key")) */
/*@
  insert :: forall < q :: (number) => prop >.
    (p:<t>+null, k:number<q>)/t |-> in:rbtree[number<q>]<{\h v -> v < h},{\h v -> v > h}>
         => {v:<u>+null | v != null}
            / a |-> lft:rbtree[{v:number<q> | v < field(out,"key")}]<{\h v -> v < h},{\h v -> v > h}>
            * b |-> rgt:rbtree[{v:number<q> | v > field(out,"key")}]<{\h v -> v < h},{\h v -> v > h}>
            * u |-> out:{ color : { v:number | (((v != 0) => (bheightp(p,in) =     bheightp(field(out,"left"),lft))) &&
                                                ((v != 0) => (bheightp(p,in) =     bheightp(field(out,"right"),rgt))) &&
                                                ((v = 0)  => (bheightp(p,in) = 1 + bheightp(field(out,"left"),lft))) &&
                                                ((v = 0)  => (bheightp(p,in) = 1 + bheightp(field(out,"right"),rgt))) &&
                                                ((v = 0) || (((colorp(field(out,"left"),lft) = 0) || (colorp(field(out,"right"),rgt) = 0)) 
                                                          && ((colorp(p,in) != 0) || ((colorp(field(out,"left"),lft) = 0) && (colorp(field(out,"right"),rgt) = 0))))))
                                               }
                        , key:   number<q>
                        , left:  {v:<a>+null  | (bheightp(v,lft) = bheightp(field(out,"right"),rgt)) }
                        , right: {v:<b>+null  | (bheightp(v,rgt) = bheightp(field(out,"left"),lft))  }
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
            var root = rotate_right(p);
            return root;
          } else {
            var plr = pl.right;
            if (is_red(plr)) {
              plr.color = 0;
              p.left = rotate_left(pl);
              var root = rotate_right(p);
              return root; 
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
            var root = rotate_left(p);
            return root;
          } else {
            var prl = pr.left;
            if (is_red(prl)) {
              prl.color = 0;
              p.right = rotate_right(pr);
              var root = rotate_left(p);
              return root; 
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
