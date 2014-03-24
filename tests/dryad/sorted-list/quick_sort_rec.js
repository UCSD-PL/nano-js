/*@ include sorted-list.js */

/*@ qualif AppKeys(v:T) : keys(v)     = Set_cup(keysp(ls,ll),keysp(gs,gg)) */
/*@ qualif AppKeys(v:Ref) : keysp(v,kk) = Set_cup(keysp(ls,ll),keysp(gs,gg)) */
/*@ qualif PartKey(v:a) : keysp(x,xs) = Set_cup(keysp(field_Ref(r,"x"),as),keysp(field_Ref(r,"y"),bs)) */

/*@ qualif AppLen(v:T) : len(v)     = lenp(ls,ll)+lenp(gs,gg) */
/*@ qualif AppLen(v:Ref) : lenp(v,kk) = lenp(ls,ll)+lenp(gs,gg) */
/*@ qualif PartLen(v:a) : lenp(x,xs) = lenp(field_Ref(r,"x"),as)+lenp(field_Ref(r,"y"),bs) */

/*@ append :: forall A.
  (xk:A, ls:<l>+null, gs:<g>+null)/l |-> ll:list[A]<{\h v -> true }>
                                 * g |-> gg:list[A]<{\h v -> true }>
    => v:<k>+null
       /k |-> kk:list[A]<{\h v -> true }>                                             */
function append(xk, ls, gs) {
  if (ls == null) {
    return gs;
  }

  var n = ls.next;

  if (n == null) {
    ls.next = gs;
  } else {
    zzz = n.data;
    n = append(xk, n, gs);
    ls.next = n;
  }
  return ls;
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
    var ret = {};
    ret.x = x;
    ret.y = b;
    return ret;
  } else {
    x.next = b;
    var ret = {};
    ret.x = a;
    ret.y = x;
    return ret;
  }
}

/*@ quickSort :: forall A.
      (x:<x>+null)/x |-> in:list[A]<{\h v -> true}>
        => {v:<o>+null | (keysp(v,out) = keysp(x,in) && lenp(v,out) = lenp(x,in)) }
          /o |-> out:list[A]<{\h v -> h <= v}> */
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
