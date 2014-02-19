/*@ include tree-traversals.js */

/*@ postorder :: 
      (x:<l>+null, n:number)/l |-> in:tree[number]<{\pl l pr r v -> true},
                                                   {\pl l pr r v -> true}>
        => {v:number | (v = (n + sizep(x,in))
                    && (((x != null) => (order(out) = n + size(in) - 1)) && sizep(x,out) = sizep(x,in)))}
           /l |-> out:tree[number]<{\pl l pr r v -> 
                                     (((x != null) && (pl != null))
                                         => (v = order(l) + 1 + sizep(pr,r)))},
                                   {\pl l pr r v -> 
                                     (((x != null) && (pr != null)) 
                                         => (v = order(r) + 1))}> */
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
