/*@ infmap :: forall A B. ((A) => B, <l>)/l |-> inflist[A] => <l>/l |-> inflist[B] */
function infmap(f, xs){
  xs.data = f(xs.data);
  z = xs.next;
  infmap(f, z);
  return xs;
}

