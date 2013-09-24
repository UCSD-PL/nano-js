/*@ foo :: (<l>)/ l |-> inflist[{number|true}] => null/same */
function foo(x) {
    var n = x.next;
    if (typeof (n) == "null") {
        assert(false);
        return x;
    } else {
        return null;
    }
}
