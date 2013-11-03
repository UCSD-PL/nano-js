// Short form
/* type t:tree[A]<P :: A->A->Prop> <Q :: A->A->Prop> 
      = { key    : A
        , left  : ?tree[A<P data>]<P, Q>
        , right : ?tree[A<Q data>]<P, Q>
        }
 */

/* type tree[A] 
      exists! l |-> tree[A<P data>]<P,Q> 
            * r |-> tree[A<Q data>]<P,Q> 
            . { left:<l>+null
              , key:A
              , right:<r>+null 
              } */

/* type bst[A]
      exists! l |-> bst[{v | v < key}] 
            * r |-> bst[{v | v >= key}]
            . { left:<l>+null
              , key:A
              , right:<r>+null 
              }

t |-> t:bst[A]
==============
t |-> { left:<l>+null
      , key:int
      , right:<r>+null
      }
*
l |-> bst[{v | v < (field t key)}]      
*
r |-> bst[{v | v >= (field t key)}]      


*/

/* type heap[A] = tree[A]<{\k v -> v < k}, {\k v -> v < k}> */

/*@
  type btree[A]
       exists! l |-> lh:btree[A] * r |-> rh:btree[A]
               . me:{ left:<l>+null
                    , key:A
                    , right:<r>+null
                    }

     with hd(x)   := field(me, "key")
      and keys(x) := (if (ttag(field(me, "left")) != "null") then
                         (if (ttag(field(me, "right")) != "null") then
                             Set_cup(Set_sng(field(me, "key")), Set_cup(keys(lh),keys(rh)))
                          else
                             Set_cup(Set_sng(field(me, "key")), keys(lh)))
                      else
                         (if (ttag(field(me, "right")) != "null") then
                             Set_cup(Set_sng(field(me, "key")), keys(rh))
                          else
                             Set_sng(field(me, "key"))))
       
*/
/*@
  type heap[A]
       exists! l |-> lh:heap[{A | ((v <= field(me, "key")))}]
             * r |-> rh:heap[{A | ((v <= field(me, "key")))}]
               . me:{ left:<l>+null
                    , key:A
                    , right:<r>+null
                    }

     with hd(x)   := field(me, "key")
      and keys(x) := (if (ttag(field(me, "left")) != "null") then
                         (if (ttag(field(me, "right")) != "null") then
                             Set_cup(Set_sng(field(me, "key")), Set_cup(keys(lh),keys(rh)))
                          else
                             Set_cup(Set_sng(field(me, "key")), keys(lh)))
                      else
                         (if (ttag(field(me, "right")) != "null") then
                             Set_cup(Set_sng(field(me, "key")), keys(rh))
                          else
                             Set_sng(field(me, "key"))))
       
*/

/*@ cmpLTB :: forall A B. (A, B) => {v:boolean | (Prop(v) <=> (a < b))} */

/*@ qualif FldGt(v:a, x:b): v <= field(x, "key") */
/*@ qualif NNull(v:a, x:b): ((ttag(x) != "null") => (ttag(v) != "null")) */

/*@ swapKeys :: forall A L R P Q.
  ({v:<r> | true},<n>)/r |-> r:{ left:L, key:A, right:R }
                     * n |-> n:{ left:P, key:A, right:Q }
                    => void/r |-> r2:{ left:L, key:A, right:R }
                          * n |-> n2:{ left:P, key:{A | v <= field(r2, "key")}, right:Q } */
// function swapKeys(x,c) {
//   var ck = c.key;
//   var xk = x.key;
//   if (cmpLT(xk, ck)) {
//     var t = xk;
//     xk    = ck;
//     ck    = t; 
//     c.key = ck;
//     x.key = xk;
//   }

//   return;
// }


/*@ heapify :: forall A. (<x>)/x |-> bs:{ left:<l>+null, key:A, right:<r>+null}
                             * l |-> ls:heap[A]
                             * r |-> rs:heap[A]
                       => void/x |-> hs:{heap[A] | true} */
function heapify(x) {
  var l = x.left;
  var r = x.right;
  
  if (typeof(l) == "null")  {
    if (typeof(r) != "null") {
      xk = x.data;
      rk = r.data;
      var xk = x.key;
      var rk = r.key;
      if (cmpLT(xk, rk)) {
        r.key = xk;
        x.key = rk;
        heapify(r);
      }
    }
  } else if (typeof(r) == "null") {
    //swapRoot(x,l);
    if (typeof(l) != "null") {
      var xk = x.key;
      var lk = l.key;
      if (cmpLT(xk, lk)) {
        l.key = xk;
        x.key = lk;
        heapify(l);
      }
    }
  } else {
    var xk = x.key;
    var lk = l.key;
    var rk = r.key;
    if (cmpLT(lk,rk)) { //bug here?
      if (cmpLT(xk, rk)) {
        x.key = rk;
        r.key = xk;
        heapify(r);
        return;
      }
    } else if (cmpLT(xk, lk)) {
            //               swapRoot(x,l);
            // l = x.left;
      x.key = lk;
      l.key = xk;
      heapify(l);
      return;
    }
  }
}
