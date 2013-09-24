/*@ type tree[A] exists! l |-> tree[A] * m |-> tree[A] . { data: A, left: <l>, right:<m> } */

/*@ swapBranches :: forall A. (<t>)/t |-> tree[A] => void/t |-> tree[A] */
function swapBranches(x) {
    var l = x.left;
    var r = x.right;
    x.left  = r;
    x.right = l;

    return;
}
