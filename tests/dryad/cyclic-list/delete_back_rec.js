/*@ qualif LenX(v:a, ret:b): ((ttag(ret) != "null") => (len(v) = len(xs) - 1)) */

/*@ remove :: forall A H.
     (x:<x>,q:H)/x |-> xs:clist[A,{H | v = q}]
     => <x>+null/x |-> ys:{clist[A,{H | v = q}] | (if (ttag(lqreturn) = "null") then (len(xs) = 1) else (len(v) = len(xs) - 1))}
*/
function remove(p,q){
  var pn = p.next;
  if (isL(pn)) {
    pn = remove(projL(pn),q);
    if (typeof(pn) != "null") {
      p.next = inL(pn);
    } else {
      p.next = inR(q);
    }
    return p;
  } else {
    return null;
  }
}
