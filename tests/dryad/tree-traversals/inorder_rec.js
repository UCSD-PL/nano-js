/*@ include tree-traversals.js */

/*@ inorder :: 
      (x:<l>+null, n:number)/l |-> in:tree[number]
        => {v:number | ((v = (size(out) + n)
                     && size(out) = size(in) 
                     && lsize(out) = lsize(in) 
                     && rsize(out) = rsize(in) 
                     && ((~(Prop(nil(out)))) => ((inorderTree(out) = 1) && (order(out) = n + lsize(in))))
                     && ((x = null) => order(in) = order(out))))}
           /l |-> out:{v:tree[number] | (Prop(nil(v)) <=> Prop(nil(x)))} */
function inorder(x, n) {
  if (x == null)
    return n;
  
  var xl = x.left;
  var xr = x.right;
  var n1 = inorder(xl, n);
  x.key  = n1;
  var n2 = n1 + 1;
  var xr = x.right
  var n3 = inorder(xr, n2);
  return n3;
}
