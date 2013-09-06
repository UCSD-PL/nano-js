/*@ fold :: forall A B. (<l>, (A,B) => B, B)/l |-> inflist[A] => B/same */
function fold(l,f,b) {


  return fold(l.next, f, f(l.data,b));

}
