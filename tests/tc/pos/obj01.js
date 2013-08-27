// /*@ id :: forall A B. (x:<l>)/l |-> {a: A, b: B} => A/same */
// function id(x) {
//     return x.a;
// }

/*@ mk2 :: ()/emp => <l>/l |-> { b:number} */
// function mk2()
// {
//     var x = {};
//     if (1) {
//         x = {a:"3"};
//     } else {
//         x = {a:"5"};
//     }

//     return x;
// }

/*@ mk :: ()/emp => <l>/l |-> { a:number, b:<m>} * m |-> {c:number} */
function mk() {
    var x = 0;
    if (1) {
        x = {c:3};
    } else {
        x = {c:7};
    }
    return {a:3, b:x};
}

/*@ foo :: () => number */
// function foo() {
//     if (1) {
//       x = 3;
//     } else {
//       x = 5;
//     }
//     return x;
// }
