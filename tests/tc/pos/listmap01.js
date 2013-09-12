/*@ type nlist  inflist[number] */
/*@ type blist  inflist[boolean] */

/*@ map :: (<l>, (number) => boolean)/l |-> inflist[number] => <l>/l |-> inflist[boolean] */
function map(x,f) {
  d      = x.data;
  x.data = f(d);
  x.next = map(x.next, f);

  return x;
}
