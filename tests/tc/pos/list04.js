/*@ next :: (x:<l>)/l |-> list[number] => <m> + null/l |-> { data: number, next:<m> + null } * m |-> list[number] */
function next(x) {
  z    = x.next;
  y    = x.next;
  return x.next;
}
