/*@ include red-black.js */

/*@ find_smallest :: forall A.
  (x:<l>, k:A)/l |-> x0:rbtree[{v:A | (v > k)}]<{\h v -> h > v},{\h v -> h < v}> => 
       r:{v:A | v > k }/l |-> x1:{v:rbtree[{v:A | ((v > k) && (v >= r))}]<{\h v -> h > v},{\h v -> h < v}> | ((bheight(v) = bheight(x0)) && (col(v) = col(x0)))}
*/
function find_smallest(x, k) {
  var xl = x.left;
  var xk = x.key;
  if (xl == null) {
    return xk;
  } else {
    ret = find_smallest(xl, k);
    return ret;
  }
}

/*@ fixup_r :: forall A.
      (x:<x>, fixed:<f>)/f |-> f0:{ b : boolean }
            * x |-> x0:{ color:{v:number | ((v != 0) => ((col xl0) = 0))}, key:A, left:{v:<xl> | (Prop(nil(v)) => Prop(nil(xr0)))}, right:{v:<xr>+null | (Prop(nil(v)) => Prop(nil(xr0)))}  }
            * xl|-> xl0:{v:rbtree[{v:A | (v < (field_int x0 "key"))}]<{\h v -> h > v},{\h v -> h < v}> | (bheight v) = (bheight xr0) + 1}
            * xr|-> xr0:{v:rbtree[{v:A | (v > (field_int x0 "key"))}]<{\h v -> h > v},{\h v -> h < v}> | (((bheight v) > 1) && ((col v) = 0))} => 

<r>/r |-> r0:{v:rbtree[A]<{\h v -> h > v},{\h v -> h < v}> | (((col v) = 0) || (((col v) != 0) && ((field_int x0 "color") != 0)))}
  * f |-> f1:{ b : {v:boolean | (((Prop(v)) => ((bheight r0) = ((bheight xl0) + (if ((field_int x0 "color") = 0) then 1 else 0))))
                              && ((~Prop(v)) => (((field_int x0 "color") = 0) && ((bheight r0) = (bheight xl0)))))}}*/
// function fixup_r(x,fixed) {
//   xl = x.left;
//   var xlc = xl.color;
//   if (xlc != 0){
//     var xlr = xl.right
//     x.left = xlr;
//     xl.right = x;
//     x.color = 1;
//     xl.color = 0;
//     p = fixup_r(x, fixed)
//     xl.right = p;
//     return xl;
//   } else {
//     xlr = xl.right;
//     xll = xl.left;
//     xlrc = xlr.color;
//     xllc = xll.color;
//   if (xllc != 0) {
//     fixed.b = true;
//     x.left = xlr;
//     xl.right = x;
//     xl.color = x.color;
//     x.color = 0;
//     xll.color = 0;
//     return xl;
//   } else {
//     if (xlrc == 0) {
//       fixed.b = (x.color != 0);
//       xl.color = 1;
//       x.color = 0;
//       return x;
//     } else {
//       fixed.b = true;
//       xlrr = xlr.right;
//       xlrl = xlr.left;
//       xl.right = xlrl;
//       xlr.left = xl;
//       xlr.right = x;
//       x.left = xlrr;
//       xlr.color = x.color;
//       x.color = 0;
//       return xlr;
//     }
//   }
//   }
// }

/*@ qualif FldLt(v:number, x:Rec): v > (field_int x "key") */
/*@ qualif FldLt(v:number, x:Rec): v = (field_int x "key") */
/*@ qualif FldLt(v:number, x:Rec): v < (field_int x "key") */

/*@ qualif FldLt(v:Rec, x:number): v > (field_int x "key") */
/*@ qualif FldLt(v:Rec, x:number): v = (field_int x "key") */
/*@ qualif FldLt(v:Rec, x:number): v < (field_int x "key") */

/*@
rbt_delete :: forall A.
(x:<a>+null, k:{v:A | true}, fixed:<f>)/f |-> f0:{ b: boolean } 
                                           * a |-> r0:rbtree[A]<{\h v -> h > v},{\h v -> h < v}> =>
                         <z>+null/f |-> f1:{ b:{v: boolean | (Prop(v) => ((bheight r0) = (bheight r1)))} }
                                * z |-> r1:{v:rbtree[A]<{\h v -> h > v },{\h v -> h < v }> | ((((col v) != 0) => ((col r0) != 0)))}

  */
function rbt_delete(x, k, fixed)
{
  if (x == null) {
    fixed.b = true;
    return x;
  } else {
    var xk = x.key;
    var xl = x.left;
    var xr = x.right;
    assume(xk == k);
    assume(xl != null);
    assume(xr != null);
    var min = find_smallest(xr, xk);
    x.key = min;
    assert (xk < min);
    var n = rbt_delete(xr, min, fixed);
    x.right = n;
    var b = fixed.b;
    assume(b);
    return x;
  }
}

