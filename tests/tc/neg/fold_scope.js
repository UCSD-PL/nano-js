/*@ bad_scope :: forall A. (<l>)/l |-> list[A] => <m> + null/m |-> list[A] */
function bad_scope(l) {
    var m = l.next;
    return m;
}
