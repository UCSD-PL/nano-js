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
    }  else {
      p.next = inR(q);
    } 
    return p;
  }
  return null;
}
/*@ include cyclic_list.js */

/*@ remove2 :: (x:<x>)/x |-> xs:clist[number,<x>]
                    => {v:<x>+null | ((len(xs) > 1) => (v != null))}
                       /x |-> ys:{v:clist[number,<x>] | ((len(xs) > 1) => (len(v) = len(xs) - 1))} */
function remove2(x){
  var xn = x.next;
  if (isL(xn)) {
    var t  = projL(xn);
    var u  = t.next;
    x.next = u;
    return x;
  } else {
    return null;
  }
}
/*@ include cyclic_list.js */

/*@ qualif Keyz(v:a): keys(v) = Set_cup(Set_sng(k), keys(xs)) */
/*@ qualif Lenz(v:a): len(v) = len(xs) + 1 */

/*@ insert :: forall A H. (p:<p>,k:A)/p |-> xs:clist[A,H]
                              => void/p |-> ys:{v:clist[A,H] | ((keys(v) = Set_cup(Set_sng(k), keys(xs)))
                                                             && (len(v)  = len(xs) + 1)) }
*/
            

function insert(p,k){
  var n = p.next;
  if (isL(n)) {
    //keep going
    var p2 = projL(n);
    insert(p2, k);
    var zzz = p2.data;
    p.next = inL(p2);
    return;
  } else {
    //at the end
    z = {};
    z.data = k;
    z.next = n;
    p.next = inL(z);
    return;
  }
}
/*@ include cyclic_list.js */



/*@ insert2 :: 
      (x:<x>, k:number)/x |-> xs:clist[number,<x>]
        => void/x |-> ys:{v:clist[number,<x>] | ((keys(v) = Set_cup(Set_sng(k), keys(xs)))
                                              && (len(v) = len(xs) + 1))}
 */
function insert2(x, k){
  var z  = {};
  t = x.next;
  z.data = k;
  z.next = t;
  x.next = inL(z);
  return;
}
