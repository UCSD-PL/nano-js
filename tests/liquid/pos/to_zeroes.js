/*@ to_zeroes :: (<l>)/ l |-> list[{number|v = 0}] => void/l |-> list[{number | true }] */
function to_zeroes(x) {
    var xn = x.next;
    x.data = 1;

    if (typeof(xn) != "null") {
    }  else {
        assert(typeof(x.next) == "null");
    }

    return;
}
    
