/*@
type list[]
        exists! l |-> tl:list[].
          r:{ next : <l> + null }
*/

/* partition :: forall A.
   (piv:A, x:{v:<x>+null | ((Prop(nil(v))) => Prop(nil(xs)))})/x |-> xs:list[][A]<{\h v -> true}>
     => <r>/a |-> as:{v:list[][A]<{\h v -> true}> | len(v) = len(as) + len(xs)} * b |-> bs:list[][A]<{\h v -> true}>
                * r |-> r:{x:{v:<a>+null | ((Prop(nil(v))) => Prop(nil(as)))}, y:{v:<b>+null | ((Prop(nil(v))) => Prop(nil(bs)))}}                */

/*@ nondet :: () => number */

/*@ partition :: 
   (xptr:<x>+null)/x |-> xs:list[]
     => partret:<a>/r |-> as:list[] * b |-> bs:list[] * a |-> xxx:{x:<r>+null, y:<b>+null}                */
function partition(xptr){
  if (xptr == null) {
    var ret = {x:null,y:null};
    return ret;
  } else { 
  
  var piv = nondet();
  var xn = xptr.next;
  var yz = partition(xn);

  a = yz.x;
  assert(a == null);
  if (0 < piv) {
    xptr.next = null;
    var ret = {x:xptr, y:a};
    return ret;
  } else {
    xptr.next = null;
    var ret = {x:a, y:xptr};
    return ret;
  }
  }
}

/*@ quicksort :: 
      (x:<x>+null)/x |-> in:list[] => {v:<o>+null | true}/o |-> qs:list[] 
*/
function quicksort(x) {
  var z = partition(x);
  // e = z.y;
  // if (d != null) {
  //   var kk = d.next;
  // }
  return z.x;
}
