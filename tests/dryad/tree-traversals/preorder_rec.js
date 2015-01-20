/*@ include tree-traversals.js */

/*@ preorder :: 
      (x:<l>+null, n:number)/l |-> in:tree[number]
        => {v:number |  (v = (n + sizep(x,in))
                     && ((x != null) => ((preorderTree(out) = 1)
                                     && (order(out) = n)) && sizep(x,out) = sizep(x,in))) }
           /l |-> out:tree[number] */
function preorder(x, n) {
  if (x == null) {
    return n;
  }
  
  x.key  = n;
  var sl = preorder(x.left, n+1);
  var sr = preorder(x.right, sl);
  return sr;
}

