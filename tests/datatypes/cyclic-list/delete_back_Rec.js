/*@ include cyclic_list.js */
/*@ qualif LenX(v:a, x:b, ret:b): (if (x != null) then (len(v) = len(xs) - 1) else (len(xs) = 1)) */

/* remove :: forall H.
   (x:<x>,q:H)/x |-> xs:clist[number,{v:H | v = q }]
      => r:{v:<x>+null | (if (v != null) then 
                            (len(out) = len(xs) - 1)
                         else
                            (len(xs) = 1))}/x |-> out:clist[number,{v:H | v = q}]*/
/*@ remove :: forall H.
   (x:<x>,q:H)/x |-> xs:clist[number,H] => r:<x>+null/x |-> out:clist[number,H] */
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

/*@ delete_back :: (x:{v:<x> | true})/ x |-> xin:{ data:number, next:either[<y>,<x>]} 
                                     * y |-> yin:clist[number,<x>]
                 => <x>+null/x |-> rout:clist[number,<x>]  */
function delete_back(x) {
  var n = x.next;
  if (isL(n)) {
    var nn = projL(n);
    foo = remove(nn, x);
    if (foo == null) {
      x.next = inR(x);
      return x;
    }  else {
      x.next = inL(foo);
      return x;
    }
  } else {
    return null;
  }
}
