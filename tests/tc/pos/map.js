/*@ map :: forall A B. ((A) => B, <l>)/l |-> list[A] => <l>/l |-> list[B] */
function map(f, xs) {
    xs.data = f(xs.data);

    if (xs.next) {
        xs.next = map(f, xs.next);
    } else {
        //shouldn't have to do this...?
        xs.next = null;
    }

    return xs;
}
// /*@ map2 :: forall A B. ((A) => B, <l>+null)/l |-> list[A] => <l>+null/l |-> list[B] */
// function map2(f, xs){
//   if (empty(xs)) {
//     return nil();
//   }

//  var y   = f(xs.data);
//  var ys  = map(f, xs.next);
//  xs.data = y;
//  xs.next = ys;
//  return xs;
// }

