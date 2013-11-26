/*@ swapBranches :: forall A. (<t>)/t |-> tree[A] => void/t |-> tree[A] */
function swapBranches(x) {
    var l = x.left;
    var r = x.right;
    x.left  = r;
    x.right = l;

    return;
}
