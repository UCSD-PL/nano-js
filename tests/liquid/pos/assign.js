/*@ assign :: (<l>)/l |-> {n:{number | true}} => number/same */
function assign(x) {
    x.n = 3;
    return x.n;
}
