/*@ include cyclic_list.js */



/* insert :: 
      (x:<x>, k:number)/x |-> xs:clist[number,<x>]
        => void/x |-> ys:{v:clist[number,<x>] | ((keys(v) = Set_cup(Set_sng(k), keys(xs)))
                                              && (len(v) = len(xs) + 1))}
 */
// function insert(x, k){
//   var z  = {};
//   t = x.next;
//   z.data = k;
//   z.next = t;
//   x.next = inL(z);
//   return;
// }

/*@ insert_VCDryad :: 
      (x:<x>, k:number)/x |-> xs:{data:number, next:either[<y>,<x>]}
                      * y |-> clist[number,<x>]
        => <r>/x |-> xs2:{data:number, next:{v:either[<r>,<x>] | ttag(v) = "inl"}} 
             * r |-> clist[number,<x>]
 */
function insert_VCDryad(x, k){
  var z  = {};
  t = x.next;
  z.data = k;
  z.next = t;
  x.next = inL(z);
  return z;
}
