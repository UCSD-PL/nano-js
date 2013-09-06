/*@ map :: forall A B. ((A) => B, <l>+null)/l |-> list[A] => <m>+null/m |-> list[A] */
function map(f, xs){
  if (empty(xs)) {
    return nil();
  }

  var y   = f(xs.data);
  
  var ys = map(f, xs.next);

  return cons(y, ys);
}

