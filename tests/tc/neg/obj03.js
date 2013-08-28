/*@ mk :: ()/emp => <l>/l |-> { a:number, b:<m>} * m |-> {c:number} */
function mk() {
    var x = 0;
    if (1) {
        x = {c:7};
    } else {
        x = {c:"3"};
    }
    return {a:3, b:x};
}
