/*@ type tree[A] exists! l |-> tree[A] . { data: A, left: <l>, right:<l> } */

/*@ buildTree :: forall A. (<l>,A)/l |-> tree[A] => <t>/t |-> tree[A] */
function buildTree(l,x) {
    var t = { data:x, left:l, right:l };
    return t;
}
