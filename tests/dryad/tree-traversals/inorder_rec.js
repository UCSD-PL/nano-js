/*@ include tree-traversals.js */
/*@ inorder :: 
      (x:<l>+null, n:number)/l |-> in:tree[number]<{\pl l pr r v -> true},{\pl l pr r v -> true}>
        => {v:number | (v = sizep(x,out) + n)}
           /l |-> out:{v:tree[number]<{\pl l pr r v -> ((x != null && pl != null) => (v = (1 + order(l) + rsize(l))))},
                                      {\pl l pr r v -> ((x != null && pr != null) => ((order(r) = (v + lsize(r) + 1))))}>
                        | (((x != null) => ((order(v) = (n + lsize(v))) && (size(v) = 1 + lsize(v) + rsize(v))))
                        && size(v) = size(in))} 
*/
function inorder(x, n) {
  if (x == null) {
    return n;
  } else {
    var xl = x.left;
    var n1 = inorder(xl, n);
    x.key  = n1;
    var n2 = n1 + 1;
    var xr = x.right
    var n3 = inorder(xr, n2);
    return n3;
  }
}
