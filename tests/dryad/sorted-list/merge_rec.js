//import "sorted-list.js";
/*@ qualif MinEq(v:a, x:b): min(v) = min(x) */
/*@ qualif MinEq(v:a, x:b): v >= min(x) */
/*@ qualif MinEq(v:a, x:b): v <= min(x) */
/*@ qualif MinEq(v:a, x:b, y:c): ((min(x) <= min(y)) ? (v >= min(x)) : (v >= min(y))) */
/*@ qualif NNull(v:a, x:b, y:c): ((ttag(v) = "null") <=> ((ttag(x) = "null") && (ttag(y) = "null"))) */

/* merge :: (x1:<a>+null, x2:<b>+null)/a |-> as:sList[{number | v >= min(as)}] * b |-> bs:sList[{number | v >= min(bs)}]
                            => {v:<c>+null | ((ttag(v) = "null") <=> ((ttag(x1) = "null") && (ttag(x2) = "null")))}
                            /c |-> cs:{sList[{number | v >= min(cs)}] | (if (ttag(x1) = "null")
                                                          then (if (ttag(x2) = "null")
                                                                   then true
                                                                   else (min(v) = min(bs)))
                                                          else (if (ttag(x2) = "null")
                                                                   then (min(v) = min(as))
                                                                   else ((min(as) <= min(bs)) ? (min(v) = min(as)) : (min(v) = min(bs)))))}
*/


/*@ merge :: forall A. (x1:<a>+null, x2:<b>+null)/a |-> x1s:sList[A] * b |-> x2s:sList[A]
                                => {v:<m>+null | ((ttag(v) = "null") <=> ((ttag(x1) = "null") && (ttag(x2) = "null"))) }
                                  /m |-> ms:{sList[A] | true }

*/
// (if (ttag(x1) = "null")
//                                                             then (if (ttag(x2) = "null")
//                                                                      then true
//                                                                      else (min(v) = min(x2s)))
//                                                             else (if (ttag(x2) = "null")
//                                                                      then (min(v) = min(x1s))
//                                                                      else (min(v) = (min(x1s) < min(x2s) ? min(x1s) : min(x2s)))))
// function merge(x1, x2){
//   if (typeof(x1) == "null"){
//     return x2;
//   }
  
//  if (typeof(x2) == "null"){
//    return x1;
//  }
//   var x1k = x1.data;
//   var x2k = x2.data;
  
//   if (cmp(x1k,x2k)){
//     var n   = x1.next;
//     var y   = merge(n, x2);
//     x1.next = y;
//     return x1;       // DRYAD: return {data : x1.data, next : y};
//   } else { 
//     //x1k > x2k
//     var y   = merge(x1, x2.next);
//     x2.next = y;
//     return x2;      // DRYAD: return {data : x2.data, next: y} ;
//   }
// }
// NOT IN DRYAD

/* split :: (x:list[A]) => {0: list[A], 1:list[A]} */

/* split :: (x:list[A]) => {0: <?l0>, 1:<?l1>}/l0 |-> list[A] * l1 |-> {v:list[A] | keys(x, h) = Set_cup(keys("0"), keys("1"))} */

/*@ split :: forall A. (<l>+null)/l |-> list[A] =>
                              <r>/r |-> {x:<x>+null, y:<y>+null}
                                * x |-> list[A]
                                * y |-> list[{A | true}] */
// function split(x){
//   if (typeof(x) == "null"){
//     r = {x:null, y:null};
//     return r;
//   } 
  
//   var xn = x.next;

//   if (typeof(xn) == "null"){
//     r = {x:x, y:null};
//     return r;
//   } else {
//     var xnn = xn.next;
//     var yz  = split(xnn);
//     var y   = yz.x;
//     var z   = yz.y;
//     x.next  = y;
//     xn.next = z;
//     r = {x:x, y:xn};
//     return r;
//   }
// }

// // not IN DRYAD

// /* sort :: (x:?list[A]) => {v: ?incList[A] | keys(v) = keys(x,h)} */
// /* sort :: (x:?list[A]) => ?incList[A] */

/*@ sortList :: forall A. (x:<j>+null)/j |-> list[A] => <k>+null/k |-> sList[{A | true}] */
function sortList(x) {
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
