/*@ map :: forall A B. ((A) => B, <l> + null)/l |-> list[A] => <m>/m |-> list[B] */
function map(f, xs){
  if (empty(xs)) {
    return nil();
  }

  unwind(xs);
  var y   = f(xs.data);
  
  var ys = map(f, xs.next);

  return cons(y, ys);

}

