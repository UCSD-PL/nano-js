/*@ measure min :: (sList[number]) => number */
/*@ cmp :: forall A. (x:A, y:A) => {v:boolean | (Prop(v) <=> (x <= y))} */

/*@ type sList[A] exists! l |-> tl:sList[{v:A | (v >= field(me, "data"))}] . me: { data:A, next:<l>+null }
  with min(x) := field(me, "data")
  and keys(x) := (if ((ttag (field me "next")) = "null") then (Set_sng (field me "data")) else (Set_cup (Set_sng (field me "data")) (keys tl)))
*/

/*@ insert :: forall A. (x:<l>+null, k:A)/l |-> in:sList[A]
                                   => <k>/k |-> out:{sList[A]
                                               | (if (ttag(x) != "null")
                                                      then ((if (min(in) < k)
                                                           then (min(v) = min(in))
                                                           else (min(v) = k)) && (keys(v) = Set_cup(Set_sng(k), keys(in))))
                                                      else ((min(v) = k) && (keys(v) = Set_sng(k)))) } */

function insert(x, k){
  if (typeof(x) == "null"){
    // x == null
    var y  = {};
    y.data = k;
    y.next = null;
    return y;
  } else {
    var xk = x.data;
    if (cmp(k,xk)){
      var y  = {};
      y.data = k;
      y.next = x;
      return y;
    } else {
      var y = x.next;
      var t = insert(y, k);
      x.next = t;
      return x;
    }
  }
}
