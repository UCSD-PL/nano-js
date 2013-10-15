//import "sorted-list.js";

/* merge :: (x1:?incList[A], x2:?incList[A]) => ?incList[A] */

/* merge :: (x1:?incList[A], x2:?incList[A]) => <?l>/l|-> {v:incList[A] | keys(v) = Set_cup(keys(x1,h), keys(x2,h))} */

/*@ merge :: (x1:<a>+null, x2:<b>+null)/a |-> list[number] * b |-> list[number] => <c>+null/c |-> list[{number|true}] */
function merge(x1, x2){
  if (typeof(x1) == "null"){
    return x2;
  }
  
 if (typeof(x2) == "null"){
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
// NOT IN DRYAD

/* split :: (x:list[A]) => {0: list[A], 1:list[A]} */

/* split :: (x:list[A]) => {0: <?l0>, 1:<?l1>}/l0 |-> list[A] * l1 |-> {v:list[A] | keys(x, h) = Set_cup(keys("0"), keys("1"))} */

/*@ split :: (<l>+null)/l |-> list[number] => <r>/r |-> {x:<x>+null, y:<y>+null} * x |-> list[number] * y |-> list[{number | true}] */
function split(x){
  if (typeof(x) == "null"){
    r = {x:null, y:null};
    return r;
  } 
  
  var xn = x.next;

  if (typeof(xn) == "null"){
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

// not IN DRYAD

/* sort :: (x:?list[A]) => {v: ?incList[A] | keys(v) = keys(x,h)} */
/* sort :: (x:?list[A]) => ?incList[A] */

/*@ sortList :: (x:<j>+null)/j |-> list[number] => <k>+null/k |-> list[{number | true}] */
function sortList(x){
  if (typeof(x) == "null"){
    return x;
  }
  var xn = x.next;
  if (typeof(xn) == "null") {
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
