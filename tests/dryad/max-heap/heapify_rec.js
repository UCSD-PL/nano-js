// Short form
/*@ type tree[A]<P :: A->A->Prop> <Q :: A->A->Prop> 
      = { key    : A
        , left  : ?tree[A<P data>]<P, Q>
        , right : ?tree[A<Q data>]<P, Q>
        }
 */

/*@ type tree[A] 
      exists! l |-> tree[A<P data>]<P,Q> 
            * r |-> tree[A<Q data>]<P,Q> 
            . { left:<l>+null
              , key:A
              , right:<r>+null 
              } */

/*@ type heap[A] = tree[A]<{\k v -> v < k}, {\k v -> v < k}> */

/*@ swapRoot :: (<p>,<c>+null)/p |-> heap[{number|true}] * c |-> heap[number] => void/same*/
function swapRoot(x,c) {
    if (typeof(c) != "null") {
        var ck = c.key;
        var xk = x.key;
        if (ck > xk) {
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
function heapify(x) {
    var s = 0;

    if (typeof(x) == "null") {
        return;
    }

    var l = x.left;
    var r = x.right;

    if (typeof(l) == "null")  {
        swapRoot(x,r);
        r = x.right;
        heapify(r);
    } else {
        if (typeof(r) == "null") {
            swapRoot(x,l);
            heapify(l);
        } else {
            var lk = l.key;
            var rk = r.key;
            if (lk < rk) {
                swapRoot(x,r);
                r = x.right;
                heapify(r);
            } else {
                swapRoot(x,l);
                l = x.left;
                heapify(l);
            }
        }
    }
    return;
}
