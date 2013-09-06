/*@ type nlist  list[number] */

/*@ type blist  list[boolean] */

/*@ append :: (x:<l>, number)/l |-> nlist => <m>/l |-> nlist * m |-> blist */
function append(x, a) {
  return { data: a , next: x };
}

