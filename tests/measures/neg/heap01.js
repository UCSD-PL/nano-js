/*@ inc :: ({v:<l> | true})/l |-> x:{n:number} => void/l |-> y:{n:{number | v > (field x "n") }} */
function inc(p) {
    var a = p.n;
    
    if (a < 4) {
        p.n = 5;
    } else {
        var b = a+1;
        p.n = b;
    }

    return;
}
