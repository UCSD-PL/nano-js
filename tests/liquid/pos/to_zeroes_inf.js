/*@ to_zeroes :: (<l>)/ l |-> inflist[{number|v = 0}] => <l>/l |-> inflist[{number | v = 1}] */
function to_zeroes(x) {
    x.data = 1;
    to_zeroes(x.next);
    return x;
}
    
