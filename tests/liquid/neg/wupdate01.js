/*@ foo :: (<l>+<m>)/l |-> {n:{number|v = 3}} * m |-> {n:{number | v = 1}} => void/l |-> {n:{number| v >= 0}} * m |-> {n:{number | v >= 0}} */
function foo(p) {
    p.n = 0;
    return;
}
