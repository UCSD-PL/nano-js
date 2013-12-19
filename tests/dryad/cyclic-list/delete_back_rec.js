/*@ include cyclic_list.js */
/*@ qualif LenX(v:a, ret:b): ((ret != null) => (len(v) = len(xs) - 1)) */

/*@ remove :: forall A H.
     (x:<x>,q:H)/x |-> xs:clist[A,{H | v = q}]
      => r:<x>+null/x |-> ys:{clist[A,{H | v = q}] | (if (r != null) then
                                                         (len(v) = len(xs) - 1)
                                                      else
                                                         (len(xs) = 1))}
*/
function remove(p,q){
  var pn = p.next;
  if (isL(pn)) {
    pn = remove(projL(pn),q);
    if (pn != null) {
      p.next = inL(pn);
    } else {
      p.next = inR(q);
    }
    return p;
  } else {
    return null;
  }
}
