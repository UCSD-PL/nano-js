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
  type heap[A]
       exists! l |-> lh:heap[{A | v <= field(me, "key")}] * r |-> rh:heap[{A | v <= field(me, "key")}]
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

/*@ cmpLTB :: forall A B. (A, B) => {v:boolean | (Prop(v) <=> (a < b))} */

/*@ swapRoot :: forall A.
  ({v:<p> | true},<c>+null)/p |->  ps:btree[A] * c |->  cs:btree[A]
                    => void/p |-> pss:btree[A] * c |-> css:btree[A] */
function swapRoot(x,c) {
    if (typeof(c) != "null") {
        var ck = c.key;
        var xk = x.key;
        if (cmpLT(ck, xk)) {
            var t = xk;
            xk    = ck;
            ck    = t; 
            c.key = ck;
            x.key = xk;
            return;
        }
    }
    return;
}

/*@ heapify :: (<x>+null)/ x |-> heap[{number|true}] => void/x |-> heap[number] */
// function heapify(x) {
//     var s = 0;

//     if (typeof(x) == "null") {
//         return;
//     }

//     var l = x.left;
//     var r = x.right;

//     if (typeof(l) == "null")  {
//         swapRoot(x,r);
//         r = x.right;
//         heapify(r);
//     } else {
//         if (typeof(r) == "null") {
//             swapRoot(x,l);
//             heapify(l);
//         } else {
//             var lk = l.key;
//             var rk = r.key;
//             if (lk < rk) {
//                 swapRoot(x,r);
//                 r = x.right;
//                 heapify(r);
//             } else {
//                 swapRoot(x,l);
//                 l = x.left;
//                 heapify(l);
//             }
//         }
//     }
//     return;
// }
