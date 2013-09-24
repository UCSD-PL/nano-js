/*@ type tree[A] exists! l |-> tree[A] * m |-> tree[A] . { data: A, left: <l>, right:<m> } */

/*@ getData :: forall A. (<t>)/t |-> tree[A] => A/t |-> tree[A] */
function getData(x) {
    var d = x.data;
    return d;
}
