/*@ foo :: (<l>,<m>)/l |-> {a:{number | v > 0}}*m |-> {a:{number | v < 0}}
             => void/l |-> {a:{number | v < 0}}*m |-> {a:{number | v > 0}} */
function foo(p,q) {
    var x = p.a;
    p.a   = -1;
    q.a   = x;
    return;
}
