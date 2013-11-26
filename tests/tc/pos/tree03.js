/*@ buildTree :: forall A. (<l>,A,<r>)/l |-> tree[A] * r |-> tree[A] => <t>/t |-> tree[A] */
function buildTree(l,x,r) {
    var t = { data:x, left:l, right:r };
    return t;
}
