/*@ inc :: (p:<l>)/l |-> x:{n:number} => void/l |-> y:{n:{number | v = (field x "n") + 1 }} */
function inc(p) {
    var a = p.n;
    p.n = a + 1;

    return;
}

/*@ call_inc :: (a:number) => <l>/l |-> z:{n:{v:number | v = a + 1 }} */
function call_inc(a) {
    var r = { n: 0 };

    if (a == 1) {
        inc(r);
    } else {
        r.n = a;
    }
    inc(r);
    return r;
}

