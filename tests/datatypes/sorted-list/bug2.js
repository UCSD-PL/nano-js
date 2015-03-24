/*@
type list[]
        exists! l |-> tl:list[]. 
          r:{ next : {v:<l> + null | (Prop(nil(v)) => Prop(nil(tl)))} }
*/

/*@ partition :: 
   (x:<x>+null)/x |-> xs:list[]
     => ret:<r>/a |-> as:list[] * b |-> bs:list[] * r |-> r:{x:<a>+null, y:<b>+null}  */
function partition(x){
  if (x == null) {
    var ret = {x:null, y:null};
    return ret;
  }

  // var xn = x.next;
  var xn = x.next;
  var yz = partition(xn);
  var a = yz.x;
  var b = yz.y;
  x.next = a;
  ret = {x:x, y:b};
  return ret;
}

/*@ quickSort ::
      (x:<x>)/x |-> in:list[]
        => <o>+null/o |-> out:{v:list[] | true }*/ 
function quickSort(x) {
  var yz  = partition(x);
  return null;
}
