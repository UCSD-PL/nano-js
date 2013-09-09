/*@ fold :: forall A B. (<l>, (A,B) => B, B)/l |-> inflist[A] => B/same */
function fold(l,f,b) {
  var n = l.next;
  var d = l.data;
  return fold(n, f, f(d,b));
  // return fold(l.next, f, f(l.data,b));

}
