/*@ include sorted-list.js */

/*@ merge :: forall A.
  (x1:<a>+null, x2:<b>+null)/a |-> x1s:incList[A]
                           * b |-> x2s:incList[A]
    => {v:<m>+null | keysp(v,ms) = Set_cup(keysp(x1,x1s),keysp(x2,x2s))} 
       /m |-> ms:incList[A]
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
  
  if (cmp(x1k,x2k)){
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

/*@ split :: forall A.
      (x:<l>+null)/l |-> ls:list[A]
        => {v:<r> | keysp(x,ls) = Set_cup(keysp(field(r,"x"),xs),keysp(field(r,"y"),ys))}
           /r |-> r:{x:<x>+null, y:<y>+null}
          * x |-> xs:list[A]
          * y |-> ys:list[A]                                                                */
function split(x){
  if (x == null) {
    r = {x:null, y:null};
    return r;
  } 
  
  var xn = x.next;

  if (xn == null) {
    r = {x:x, y:null};
    return r;
  } else {
    var xnn = xn.next;
    var yz  = split(xnn);
    var y   = yz.x;
    var z   = yz.y;
    x.next  = y;
    xn.next = z;
    r = {x:x, y:xn};
    return r;
  }
}
/*@ sortList :: forall A.
      (x:<j>+null)/j |-> xs:list[A]
         => {v:<k>+null | keysp(v,ks) = keysp(x,xs)}
           /k |-> ks:incList[A]                       */
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
  if (ys != null) {
    if (zs != null) {
      return ret;
    } else {
      return ret;
    }
  } else {
    if (zs != null) {
      return ret;
    } else {
      return ret;
    }
  }
}
