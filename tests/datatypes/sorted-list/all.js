/*@ include sorted-list.js */

/*@ qualif Ret(v:Ref): (lenp(v,ys) = 1 + lenp(x,xs)) */
/*@ qualif Ret(v:Ref): (keysp(v,ys) = (Set_cup(keysp(x,xs), Set_sng(k)))) */

/*@ insert :: forall A.
  (x:<l>+null, k:A)/l |-> xs:list[A]<{\h v -> true}>
             => <k>/k |-> ys:list[A]<{\h v -> true}>
*/
function insert(x, k){
  if (x == null){
    var y  = { data:k, next: null };
    return y;
  } else {
    var xk = x.data;
    if (k <= xk) {
      var y  = {data: k, next: x};
      return y;
    } else {
      var y = x.next;
      var t = insert(y, k);
      x.next = t;
      return x;
    }
  }
}

/*@ insertion_sort ::  forall A.
  (x:<l>+null)/l |-> ls:list[A]<{\h v -> true}>
    => {v:<k>+null | (((v != null) => (len(ys) = len(ls)))
                  &&  ((v = null) <=> (x = null))
                  && (keysp(v,ys) = keysp(x,ls))) }/k |-> ys:list[A]<{\h v -> h <= v}>  */
function insertion_sort(x){
  if (x == null) return null;

  var xn = x.next;
  var xk = x.data;
  var t  = insertion_sort(xn);
  return insert(t, xk);
}

/*@ qualif UnionKeys(v:Ref): ((keysp(v,ms) = (Set_cup(keysp(x1,x1s), keysp(x2,x2s))))) */
/*@ qualif SplitKeys(v:Rec): ((keysp(x,ls) = (Set_cup(keysp(field_Ref(r,"x"),xs), keysp(field_Ref(r,"y"),ys))))) */

/*@ qualif LenSum(v:Ref): ((lenp(v,ms) = (lenp(x1,x1s) + lenp(x2,x2s)))) */
/*@ qualif SplitLen(v:Rec): ((lenp(x,ls) = (lenp(field_Ref(r,"x"),xs) + lenp(field_Ref(r,"y"),ys)))) */

/*@ merge :: forall A.
  (x1:<a>+null, x2:<b>+null)/a |-> x1s:list[A]<{\h v -> h <= v}> 
                           * b |-> x2s:list[A]<{\h v -> h <= v}>
    => <m>+null
       /m |-> ms:list[A]<{\h v -> h <= v}>
*/
function merge(x1, x2){
  if (x1 == null) {
    assume(0 == 1);
    return x2;
  }

 if (x2 == null) {
   return x1;
 }
  var x1k = x1.data;
  var x2k = x2.data;

  if (x1k <= x2k){
    var n   = x1.next;
    var y   = merge(n, x2);
    x1.next = y;
    return x1;       // DRYAD: return {data : x1.data, next : y};
  } else { 
    //x1k > x2k
    var y   = merge(x1, x2.next);
    x2.next = y;
    return x2;      // DRYAD: return {data : x2.data, next: y} ;
  }
}

/*@ split :: 
      (x:<l>+null)/l |-> ls:list[number]<{\h v -> true}>
        => <r>/r |-> r:{x:<a>+null, y:<b>+null} * a |-> xs:list[number]<{\h v -> h <= v}> 
                                                * b |-> ys:list[number]<{\h v -> h <= v}>      */
function split(x){
  if (x == null) {
    r = {x:null, y:null};
    return r;
  } 
 
  var xn = x.next;
  if (xn == null) {
    x.next = null;
    r = {x:x, y:null};
    return r;
  } else {
    var xnn = xn.next;
    var yz  = split(xnn);
    var a   = yz.x;
    var b   = yz.y;
    x.next  = a;
    xn.next = b;
    r = {x:x, y:xn};
    return r;
  }
}

/*@ sortList ::
      (x:<l>+null)/l |-> xs:list[number]<{\h v -> true}>
         => {v:<k>+null | (lenp(v,ks) = lenp(x,xs) && keysp(v,ks) = keysp(x,xs))}/k |-> ks:list[number]<{\h v -> h <= v}> */
function sortList(x) {
  if (x == null){
    return null;
  }

  var xn = x.next;
  if (xn == null) {
    return x;
  }

  var yz = split(x);
  var y = yz.x;
  var z = yz.y;
  var ys = sortList(y);
  var zs = sortList(z);
  var ret = merge(ys,zs);
  return ret;
}


/*@ qualif AppKeys(v:T) : keys(v)     = Set_cup(keysp(ls,ll),keysp(gs,gg)) */
/*@ qualif AppKeys(v:Ref) : keysp(v,kk) = Set_cup(keysp(ls,ll),keysp(gs,gg)) */
/*@ qualif PartKey(v:Rec) : keysp(x,xs) = Set_cup(keysp(field_Ref(r,"x"),as),keysp(field_Ref(r,"y"),bs)) */

/*@ qualif AppLen(v:T) : len(v)     = lenp(ls,ll)+lenp(gs,gg) */
/*@ qualif AppLen(v:Ref) : lenp(v,kk) = lenp(ls,ll)+lenp(gs,gg) */
/*@ qualif PartLen(v:Rec) : lenp(x,xs) = lenp(field_Ref(r,"x"),as)+lenp(field_Ref(r,"y"),bs) */

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
