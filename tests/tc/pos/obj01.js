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
        x = {c:7};
    } else {
        x = {c:3};
    }
    return {a:3, b:x};
}

/*@ setZero :: (x:number)/l |-> {a:number} => <l>/same */
function setZero(x) {
    x.a = 0;
    return x;
}

