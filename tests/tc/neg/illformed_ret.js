/*@ bad :: (<l>)/l |-> { ref:<l> } => <z>/same */
function bad(x) {
    return x;
}
