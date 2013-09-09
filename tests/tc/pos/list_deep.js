/*@ deep :: forall A. (<l>)/l |-> list[A] => <l>/same */
function deep(x) {
    xn = x.next;
    xnn = xn.next;
    xnnn = xnn.next;
    return x;
}
