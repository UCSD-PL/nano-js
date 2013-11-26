/*@ buildTree :: forall A. (<l>,A)/l |-> tree[A] => <t>/t |-> tree[A] */
function buildTree(l,x) {
    var t = { data:x, left:l, right:l };
    return t;
}
