/*@ next :: (x:<l>)/l |-> list[number] => <l> + null/l |-> list[number] */
function next(x) {
  var z    = x.next;
  // y    = x.next;
  // r    = x.next;
  return x;
}
