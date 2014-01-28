/*@ include singly-linked-list.js */

/*@ reverseLoop :: 
  (i:<i>+null, j:<j>+null)/i |-> is:list[number] * j |-> js:list[number]
    => {v:<k>+null | ((lenp(v,ks) = lenp(i,is) + lenp(j,js))
                   && (keysp(v,ks) =keysp(i,is) ∪ keysp(j,js))) }
    /k |-> ks:list[number]
*/
function reverseLoop(i, j){
  if (i != null) {
    var temp = i.next;
    i.next   = j;
    var r    = reverseLoop(temp, i);
    return r;
  } else {
    return j;
  }
}

/*@ reverse ::
  (x:<x>)/x |-> xs:list[number] => {v:<y>+null | ((lenp(v,ys) = lenp(x,xs))
                                               && (keysp(v,ys) = keysp(x,xs))) }
                              /y |-> ys:list[number]*/
function reverse(x){
  var r = reverseLoop(x,null);
  return r;
}

