/*@ foo :: (<l>)/l |-> { n:{number | true}} => void/same */

/*@ bar :: (<l>)/l |-> { n:{string | true}} => void/same */
function bar(x) {
    foo(x);
}
