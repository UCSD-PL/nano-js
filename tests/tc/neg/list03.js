/*@ type nlist list[number] */

/*@ next :: (x:<l>)/l |-> nlist => <m>/l |-> nlist * m |-> nlist */
function next(x) {
  return x.next;
}
