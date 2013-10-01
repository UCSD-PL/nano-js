/*@ type heap[A] exists! l |-> heap[A] * r |-> heap[A] . { left:<l>+null, key:A, right:<r>+null } */

/*@ foo :: (<p>,<c>+null)/p |-> heap[{number|true}] * c |-> heap[number] => void/same*/
function foo(x,c) {
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

/*@ heapify      :: (<x>+null)/ x |-> heap[{number|true}] => void/x |-> heap[number] */
function heapify(x) {
    var s = 0;

    if (typeof(x) == "null") {
        return;
    }

    var l = x.left;
    var r = x.right;

    if (typeof(l) == "null")  {
        foo(x,r);
        r = x.right;
        heapify(r);
    } else {
        if (typeof(r) == "null") {
            foo(x,l);
            heapify(l);
        } else {
            var lk = l.key;
            var rk = r.key;
            if (lk < rk) {
                foo(x,r);
                r = x.right;
                heapify(r);
            } else {
                foo(x,l);
                l = x.left;
                heapify(l);
            }
        }
    }
    return;
}
