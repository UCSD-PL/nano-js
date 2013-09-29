/*@ type heap[A] exists! l |-> heap[A] * r |-> heap[A] . { left:<l>, key:A, right:<r> } */
/*@ heapify :: (<x>)/ x |-> heap[number] => void/x |-> heap[number] */
function heapify(x) {
    var left  = x.left;
    var right = x.right;
    var s = 0;
    if (typeof(left) == "null") {
        s = right;
    } else {
        if (typeof(right) == "null") {
            s = left;
        } else {
            var lk = left.key;
            var rk = right.key;
            if (lk < rk) {
                s = right;
            } else {
                s = left;
            }
            s = right;
        }
    }
    if (typeof(s) != "null") {
       var sk = s.key;
       var xk = x.key;
        if (1/* sk > xk*/) {
            var t = xk;
            xk    = sk;
            sk    = t; 
            s.key = sk;
            x.key = xk;
            heapify(s);
        }
    }
    return;
}
