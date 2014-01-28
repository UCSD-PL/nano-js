/*@ include tree-traversals.js */
/*@ preorder :: 
      (x:<l>+null, n:number)/l |-> in:tree[number]<{\pl l pr r v -> true},{\pl l pr r v -> true}>
        => {v:number | v = n + sizep(x,in)}
           /l |-> out:{v:tree[number]<{\pl l pr r v -> (((x != null) && (pl != null)) => (order(l) = v + 1))},
                                      {\pl l pr r v -> (((x != null) && (pr != null)) => (order(r) = v + 1 + sizep(pl, l)))}> 
                        | (((x != null) => (order(v) = n)) && sizep(x,v) = sizep(x,in))} */
function preorder(x, n) {
  if (x == null) {
    return n;
  }
  x.key  = n;
  var sl = preorder(x.left, n+1);
  var sr = preorder(x.right, sl);

  return sr;
}

