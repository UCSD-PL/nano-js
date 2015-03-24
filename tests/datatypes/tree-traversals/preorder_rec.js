/*@ include tree-traversals.js */

/*@ preorder :: 
      (x:<l>+null, n:number)/l |-> xs:tree[number]
        => {v:number |  ((v = (n + size(xs)))
                     && ((preorderTree(ys) = 1))
                     && ((x != null) => (order(ys) = n)) 
                     && (size(ys) = size(xs))) }
           /l |-> ys:{v:tree[number] | (Prop(nil(v)) <=> Prop(nil(xs)))} */
function preorder(x, n) {
  if (x == null) {
    return n;
  }
  
  x.key  = n;
  var sl = preorder(x.left, n+1);
  var sr = preorder(x.right, sl);
  return sr;
}

