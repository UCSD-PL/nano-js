/*@ include sorted-list.js */

/*@ qualif Keys1(v:T,x:T,y:T): (keys(v) = Set_cup(keys(x),keys(y))) */

/*@ reverseLoop :: 
  (i:<i>+null, xd:number, j:<j>+null)/i |-> is:list[number]<{\h v -> true}> 
                                    * j |-> js:list[number]<{\h v -> true}> =>
                             <k>+null/k |-> ks:list[number]<{\h v -> true}>
*/
function reverseLoop(i, /* ghost */ xd, j){
  if (i != null) {
    var temp = i.next
    var k = i.data;
    i.next = j;
    var r    = reverseLoop(temp, k, i);
    return r;
  } else {
    return j;
  }
}

/*@ reverse ::
  (x:<x>)/x |-> xs:list[number]<{\h v -> h < v}> => 
      <y>/y |-> ys:{v:list[number]<{\h v -> v <= h}> | ((len(v) = len(xs)) && keys(v) = keys(xs))} */
function reverse(x){
  var xd = x.data;
  var xn = x.next;
  x.next = null;
  var r = reverseLoop(xn,xd,x);
  return r;
}

