/*@ type list_non_null[A]  {  data : A, 
                     next : list[A]  } */

/*@ map :: forall A B. (<l>, (A) => B)/l |-> inflist[A] => <m>/m |-> inflist[B] */
function map(x,f) {
  return { 
   data: f(x.data) , 
   next: map(x.next, f)
  };
}
