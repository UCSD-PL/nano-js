/*@ to_zeroes :: (<l>)/ l |-> xs:list[{number|v = 1}] => void/l |-> xs:list[{number | v = 0 }] */
function to_zeroes(x) {
    var xn = x.next;
    x.data = 0;

    var s = typeof(xn);
    if (typeof(xn) != "null") {
        to_zeroes(xn);
    } else {
    }

    return;
}
    
