/*@ include singly-linked-list.js */

/*@ reverseLoop :: 
  (i:<i>+null, j:<j>+null)/i |-> is:list[] * j |-> js:list[] =>
  <k>+null                /k |-> ks:list[]
*/
function reverseLoop(i, j){
  if (i != null) {
    var z = i;
    var r    = reverseLoop(null, z);
    return r;
  } else {
    return j;
  }
}

/* reverse ::
  (x:<x>)/x |-> xs:list[number] => <y>/y |-> ys:{v:list[number] | ((len(v) = len(xs)) && keys(v) = keys(xs))} */
/*@ reverse ::
  (x:<x>)/x |-> xs:list[] => <y>/y |-> ys:{v:list[] | true } */
function reverse(x){
  var r = reverseLoop(x,null);
  return r;
}

