/*@ type nlist  inflist[number] */
/*@ type blist  inflist[boolean] */

/*@ map :: (<l>, (number) => boolean)/l |-> nlist => <m>/m |-> blist */
function map(x,f) {
  d = f(x.data);
  n = map(x.next, f);
  r = {data:d, next:n};
  wind(r, inflist);
  return r;

  //return { 
  //  data: f(x.data) , 
  //  next: map(x.next, f)
  //};

}
