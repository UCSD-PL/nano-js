/*@ include cyclic_list.js */
/*@ qualif LenX(v:a, x:b, ret:b): (if (x != null) then (len(v) = len(xs) - 1) else (len(xs) = 1)) */

/*@ remove :: forall H.
   (x:<x>,q:H)/x |-> xs:clist[number,{v:H | v = q }]
      => r:{v:<x>+null | (if (v != null) then 
                            (len(out) = len(xs) - 1)
                         else
                            (len(xs) = 1))}/x |-> out:clist[number,{v:H | v = q}]*/
function remove(p,q){
  var pn = p.next;
  if (isL(pn)) {
    var ppn = projL(pn);
    pn = remove(ppn,q);
    if (pn != null) {
      p.next = inL(pn);
    } else {
      p.next = inR(q);
    }
    return p;
  }
  return null;
}
