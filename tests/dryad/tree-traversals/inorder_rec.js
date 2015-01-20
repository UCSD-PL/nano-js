/*@ include tree-traversals.js */

/*@ inorder :: 
      (x:<l>+null, n:number)/l |-> in:tree[number]
        => {v:number | ((v = (sizep(x,out) + n)
                     && sizep(x,out) = sizep(x,in) 
                     && ((x = null) => order(in) = order(out)))
                     && ((x != null) =>((inorderTree(out) = 1)&& ((order(out) = (n + lsize(out))) && (size(out) = 1 + lsize(out) + rsize(out))))))}
           /l |-> out:tree[number]*/
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
