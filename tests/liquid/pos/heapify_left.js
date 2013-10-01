/*@ type heap[A] exists! l |-> heap[A] * r |-> heap[A] . { left:<l>+null, key:A, right:<r>+null } */

/*@
  heapifyLeft  :: (<p>,<l>,xk:number,lk:number)/p |-> { left:<l>, key:{ number | v = xk }, right:<r>+null }
                                              * l |-> heap[{ number | v = lk }] * r |-> heap[number] =>
                                           void/p |-> { left:<l>, key:{ number | v >= lk }, right:<r>+null }
                                              * l |-> heap[{ number | true }] * r |-> heap[number]
*/
function heapifyLeft(x,l,xk,lk) {
    if (lk > xk) {
        l.key = xk;
        x.key = lk;
    }
    return;
}
