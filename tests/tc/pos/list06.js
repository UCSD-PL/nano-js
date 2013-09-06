/*@ type nlist list[number] */

/*@ next :: (x:<l> + null)/l |-> nlist => <m> + null/m |-> nlist */
function next(x) {

  if (1 > 0) {
    return x.next;
  }
  else 
    return null;
    
}
