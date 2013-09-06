/*@ map :: forall A B. ((A) => B,
                        {v:<l> | not (null v) } + {v:null | (null v)})/l |-> list[A]
                      => { v:<m>| not (null v) } + {v:null | (null v)}/m |-> list[B] */
function map(f, xs) {
  if (empty(xs)) {
    return nil();
  }
       
  var y   = f(xs.data);
  
  var ys = map(f, xs.next);

  return cons(y, ys);

}

