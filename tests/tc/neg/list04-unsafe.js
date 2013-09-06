/*@ type nlist  list[number] */

/*@ next :: (x:<l>)/l |-> nlist => <m>/m |-> nlist * l |-> nlist */
function next(x) {
  return x.next;
}
