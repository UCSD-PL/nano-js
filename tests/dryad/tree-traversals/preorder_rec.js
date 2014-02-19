/*@ include tree-traversals.js */
/*@ preorder :: 
      (x:<l>+null, n:number)/l |-> in:tree[number]<{\pl l pr r v -> true},{\pl l pr r v -> true}>
        => {v:number |  (v = (n + sizep(x,in))
                     && (((x != null) => (order(out) = n)) && sizep(x,out) = sizep(x,in))) }
           /l |-> out:tree[number]<{\pl l pr r v -> (((x != null) && (pl != null)) => (order(l) = v + 1))},
                                   {\pl l pr r v -> (((x != null) && (pr != null)) => (order(r) = v + 1 + sizep(pl, l)))}> */
function preorder(x, n) {
  if (x == null) {
    return n;
  }
  x.key  = n;
  var sl = preorder(x.left, n+1);
  var sr = preorder(x.right, sl);

  return sr;
}

