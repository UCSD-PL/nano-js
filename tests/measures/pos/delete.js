/*@ foo :: (<l>+null)/l |-> {n:number} => void/emp */
function foo(x) {
    if (typeof(x) != "null") {
        delete(x);
    }
    return;
}
