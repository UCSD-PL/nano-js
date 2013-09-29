/*@ foo :: forall A. (<l>)/l |-> list[A] => void/l |-> list[A] */

/*@ bar :: forall A. (A)/emp => <l>/l |-> list[A] */
function bar (x) {
    var lst = { data:x, next:null };
    foo(lst);
    return lst;
}
