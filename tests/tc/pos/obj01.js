// /*@ id :: forall A B. (x:<l>)/l |-> {a: A, b: B} => A/same */
// function id(x) {
//     return x.a;
// }

/*@ mk :: (z:<l>, m:<m>)/emp => <l>/l |-> { a:string, b:<m>} * m |-> { c:number }*/
function mk() {
    x = {c:3};
    return {a:"3", b:x};
}
