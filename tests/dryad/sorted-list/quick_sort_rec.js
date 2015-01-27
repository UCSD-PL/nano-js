/*@ include sorted-list.js */

/*@ append :: forall A.
  (xk:A, ls:<l>+null, gs:<g>+null)/l |-> ll:list[A]<{\h e -> true }>* g |-> gg:list[A]<{\h e -> true }>
    => <k>+null/k |-> kk:list[A]<{\h e -> true }>                                             */
function append(xk, ls, gs) {
  if (ls == null) {
    return gs;
  }

  var n = ls.next;

  if (n == null) {
    ls.next = gs;
    return ls;
  } else {
    zzz = n.data;
    n = append(xk, n, gs);
    ls.next = n;
    return ls;
  }
}

/*@ partition :: forall A.
   (piv:A, x:<x>+null)/x |-> xs:list[A]<{\h v -> true}>
     => <r>
                 /a |-> as:list[A]<{\h v -> true}>
                * b |-> bs:list[A]<{\h v -> true}>
                * r |-> r:{x:<a>+null, y:<b>+null}                */
function partition(piv, x){
  if (x == null) {
      var ret = {};
      ret.x = null;
      ret.y = null;
      return ret;
  }

  var xn = x.next;
  var yz = partition(piv, xn);
  var xd = x.data;
  var a = yz.x;
  var b = yz.y;

  if (xd < piv) {
    x.next = a
    var ret = {x:x, y:b};
    return ret;
  } else {
    x.next = b;
    var ret = {x:a, y:x};
    return ret;
  }
}

/*@ quickSort :: forall A.
      (x:<x>+null)/x |-> in:list[A]<{\h e -> true}>
        => r:{e:<o>+null | (Prop(nil(e)) => Prop(nil(x)))}/
           o |-> out:{v:list[A]<{\h e -> h <= e }> | ((len(v) = len(in)) && (keys(v) = keys(in)))}*/ 
function quickSort(x) {
  if (x == null){
    return null;
  }
  var piv = x.data;
  var xn  = x.next;
  var yz  = partition(piv, xn);
  var ls  = quickSort(yz.x);
  var gs  = quickSort(yz.y);
  x.next  = gs;
  var ret = append(piv, ls, x);
  return ret;
}
