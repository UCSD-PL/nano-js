/*@ id :: forall A B. (x:<l>)/l |-> {a: A, b: B} => A/same */
function id(x) {
    return x.a;
}

