/*@ type list_non_null[A]  {  data : A, 
                     next : list[A]  } */

/*@ map :: forall A B. (<l>, (A) => B)/l |-> inflist[A] => <m>/m |-> inflist[B] */
function map(x,f) {
  d = f(x.data);
  n = map(x.next, f);
  r = { data:d, next: n};
  wind(r, inflist);
  return r;
  //return { 
  //  data: f(x.data) , 
  //  next: map(x.next, f)
  //};

}
