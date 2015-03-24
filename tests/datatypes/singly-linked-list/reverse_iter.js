/*@ include singly-linked-list.js */

/*@ reverseLoop :: 
  (i:<i>+null, j:<j>+null)/i |-> is:list[number] * j |-> js:list[number] =>
  <k>+null                /k |-> ks:list[number]
*/
function reverseLoop(i, j){
  if (i != null) {
    var temp = i.next
    i.next = j;
    var r    = reverseLoop(temp, i);
    return r;
  } else {
    return j;
  }
}

/*@ reverse ::
  (x:<x>)/x |-> xs:list[number] => <y>/y |-> ys:{v:list[number] |((len(v) = len(xs)) &&  (keys(v) = keys(xs)))} 
*/
function reverse(x){
  var r = reverseLoop(x,null);
  return r;
}

