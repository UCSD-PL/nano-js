
/*@ append :: (x:<l>,number)/l |-> list[number] => <m>/m |-> list[number] */
function append(x, a) {
    var l = { data: a, next: x };
    return l;

}
