/*@ map :: forall A B. ((A) => B, <l>+null)/l |-> list[A] => <m>+null/m |-> list[B] */
function map(f, xs){
  if (empty(xs)) {
    //fold_all()
    return nil();
    //fold_all()
  } // else { fold_all() }

  var y   = f(xs.data);
  
  var ys = map(f, xs.next);

  //fold_all()
  return cons(y, ys);
}

