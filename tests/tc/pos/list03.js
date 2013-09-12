/*@ append :: forall A. (x:<l>,A)/l |-> list[A] => <m>/m |-> list[A] */
function append(x, a) {
    var l = { data: a, next: x };
    return l;
}
