/*@ include tree-traversals.js */

/*@ postorder :: 
      (x:<l>+null, n:number)/l |-> in:tree[number]
        => {v:number | ((v = (n + size(in)))
                     && ((x != null) => ((postorderTree(out) = 1))
                                     && ((order(out) = n + size(in) - 1)) && size(out) = size(in)))}
           /l |-> out:{v:tree[number] | ((Prop(nil(v)) <=> Prop(nil(x))))} */
function postorder(x, n) {
  if (x == null)
    return n;

  xl = x.left;
  xr = x.right;
  var n1 = postorder(xl, n);
  var n2 = postorder(xr, n1);
  x.key = n2;
  return n2 + 1;
}