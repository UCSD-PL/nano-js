/*@ id :: forall A B. (x:<l>)/l |-> {a: A, b: B} => A/same */
function id(x) {
//    unwind(x);
//    wind(x);
    return x.a;
}

