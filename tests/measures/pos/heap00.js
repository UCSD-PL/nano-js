/*@ foo :: (<x>,y:{number | v = (field x "n")} )/x |-> x:{n:{number | ((v > 0) && (v = (field x "n"))) }} => {number | v > 0}/same */
function foo(p,y) {
    return y;
}

/*@ bar :: (<x>)/x |-> x:{n:{number | v = (field x "n") }} => {number | v = (field x "n") }/same */
function bar(p) {
    var x = p.n;
    return x;
}

/*@ qux :: (<x>,<y>)/x |-> x:{n:number} * y |-> y:{n:number} => {number | v = (field x "n") }/same */
function qux(p,q) {
    var x = p.n;
    var y = q.n
    return x;
}

/*@ baz :: (<x>,<y>,number)/x |-> x:{n:number} * y |-> y:{n:number}
                   => void/x |-> a:{n:number} * y |-> b:{n:{number | v = field(x, "n") } } */
function baz(p,q,w) {
    var z = p.n;

    if (random() > 1)
        q.n = z;
    else
        q.n = z;

    return;
}

