/*@ deep :: forall A. (<l>)/l |-> list[A] => <l>/same */
function deep(x) {
    xn = x.next;
    if (xn) {
      xnn = xn.next;
      if (xnn) {
          xnnn = xnn.next;
      }
    }
    return x;
}
