/*@ getData :: forall A. (<t>)/t |-> tree[A] => A/t |-> tree[A] */
function getData(x) {
    var d = x.data;
    return d;
}
