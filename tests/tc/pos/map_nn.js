/*@ type nnlist[A] exists! l |-> nnlist[A]. { data: A, next: <l> }        */
/*@ nncons :: forall A. (A, <l>)/l |-> nnlist[A] => <m>/m |-> nnlist[A] */

/*@ map :: forall A B. ((A) => B, <l>)/l |-> nnlist[A] => <m>/m |-> nnlist[B] */
function map(f, xs){
  // if (empty(xs)) {
  //   return nil();
  // }

  var y   = f(xs.data);
  
  var ys = map(f, xs.next);

  return nncons(y, ys);

}

