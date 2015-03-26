/*@ include sorted-list.js */

/*@ qualif Keys1(v:T,x:T,y:T): (keys(v) = Set_cup(keys(x),keys(y))) */
/*@ qualif Keys2(v:T,x:T,y:T): (keys(x) = Set_cup(keys(v),keys(y))) */

/*@ merge :: forall A.
  (x1:<a>+null, x2:<b>+null)/a |-> x1s:list[A]<{\h v -> true}> * b |-> x2s:list[A]<{\h v -> true}>
    => <m>+null/m |-> ms:list[A]<{\h v -> true}>
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
        => <r>/r |-> r:{x:<a>+null, y:<b>+null} * a |-> xs:list[number]<{\h v -> true}> 
                                                * b |-> ys:list[number]<{\h v -> true }>      */
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

/* sortList ::
      (x:<l>+null)/l |-> xs:list[number]<{\h v -> true}>
         => {v:<k>+null | (Prop(nil(v)) => Prop(nil(x)))}/
            k |-> ks:{v:list[number]<{\h v -> h <= v}> | ((keys(v) = keys(xs)) && (len(v) = len(xs)))} */
/*@ sortList ::
      (x:<l>+null)/l |-> xs:list[number]<{\h v -> true}>
         => v:<k>+null/k |-> ks:{v:list[number]<{\h v -> h <= v}> | (keys(v) = keys(xs))} */
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