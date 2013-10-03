//import "singly-linked-list.js"

// Options:

// 1. Implicit parameters for input set of KEYS (in general, pre-state values)
/* copy :: Πks. ({x:list[A] | keys(x) = ks}) => {v:list[A] | keys(v) = ks * keys(x) = ks} */

// clearly terrible for inference -- where do these `ks` come from?
/* copy :: Πks. ({x:list[A] | keys(x) = ks}) => {v:list[A]} / v |-> keys(v) = ks * | x |-> keys(x) = ks */


// 2. NAMED heaps, measures take heap-name as parameter.

// In below, separation between x and v in output is NOT obvious.
/* copy ::(x:list[A])/h1 => {v:list[A]| keys(x,h1) == keys(x,h2) == keys(v,h2)}/h2 */


// In below, separation between x and v in output IS obvious.
/* copy ::(x:list[A])/h1 => {v:list[A]}/ v|-> keys(v) = keys(x,h1) * x |-> keys(x) == keys(x,h1)} */

/*@ copy :: forall A. (x:<l>+null)/l |-> list[A] => <m>+null/l |-> list[A] * m |-> list[A] */
function copy(x){
  if (typeof(x) == "null"){
    return null;
  } else {
    var u  = copy(x.next);
    var t  = {data: x.data, next : u};
    // var t = {}; t.data = x.data; t.next = u;
    return t;
  } 
}

