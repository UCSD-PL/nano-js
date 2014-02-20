/*@ include sorted-list.js */
/*@ qualif UnionKeys(v:a): ((keysp(v,ms) = (keysp(x1,x1s) ∪ keysp(x2,x2s)))) */
/*@ qualif SplitKeys(v:a): ((keysp(x,ls) = (keysp(field(r,"x"),xs) ∪ keysp(field(r,"y"),ys)))) */

/*@ merge :: forall A.
  (x1:<a>+null, x2:<b>+null)/a |-> x1s:list[A]<{\h v -> h <= v}> 
                           * b |-> x2s:list[A]<{\h v -> h <= v}>
    => <m>+null
       /m |-> ms:list[A]<{\h v -> h <= v}>
*/
function merge(x1, x2){
  if (x1 == null) {
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
         => {v:<k>+null | keysp(v,ks) = keysp(x,xs)}/k |-> ks:list[number]<{\h v -> h <= v}> */
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