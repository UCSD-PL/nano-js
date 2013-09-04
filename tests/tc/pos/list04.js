/*@ type nlist  list[number] */ 

/*@ next :: (x:<l>)/l |-> nlist => <m> + null/l |-> { data: number, next:<m> + null } * m |-> nlist */
function next(x) {
  unwind(x);
  return x.next;
}
