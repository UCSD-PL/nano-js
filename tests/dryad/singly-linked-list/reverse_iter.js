//import "singly-linked-list.js"

/*@ reverseLoop :: forall A.
  (i:<i>+null, j:<j>+null)/i |-> is:list[A] * j |-> js:list[A]
    => {v:<k>+null | ((lenp(v,ks) = lenp(i,is) + lenp(j,js))
                   && (keysp(v,ks) = Set_cup(keysp(i,is),keysp(j,js)))) }
    /k |-> ks:list[A]
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

/*@ reverse :: forall A.
  (x:<x>)/x |-> xs:list[A] => {v:<y>+null | ((lenp(v,ys) = lenp(x,xs))
                                          && (keysp(v,ys) = keysp(x,xs))) }
                              /y |-> ys:list[A]*/
function reverse(x){
  var y = null;
  var r = reverseLoop(x,y);
  return r;
}

