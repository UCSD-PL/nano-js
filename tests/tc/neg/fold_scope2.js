/*@ bad_scope :: forall A. (<l>)/l |-> inflist[A] => <m>/m |-> inflist[A] */
function bad_scope(l) {
    var m = l.next;
    return m;
}
