/*@ foo :: (<l>)/l |-> {a:{number | true}} => void/l |-> {a:{number | v > 0 }} */
function foo(p) {
    if (random()) {
        p.a = 3;
    } else {
        p.a = 5;
    }
    return;
}
