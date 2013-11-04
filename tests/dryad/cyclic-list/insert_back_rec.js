// DROP the refinement on the output. the dryad postcondition is lame (and has 
// no mention of keys.

/*@ qualif Keyz(v:a): keys(v) = Set_cup(Set_sng(k), keys(xs)) */
/*@ qualif Lenz(v:a): len(v) = len(xs) + 1 */

/*@ insert :: forall A H. (p:<p>,k:A)/p |-> xs:clist[A,H]
                             => void/p |-> ys:{clist[A,H] | ((keys(v) = Set_cup(Set_sng(k), keys(xs)))
                                                          && (len(v)  = len(xs) + 1)) }
*/
            

function insert(p,k){
  var n = p.next;
  if (isL(n)) {
    //keep going
    var p2 = projL(n);
    insert(p2, k);
    p.next = inL(p2);
  } else {
    //at the end
    z = {};
    z.data = k;
    z.next = n;
    p.next = inL(z);
  }
  return;
}
