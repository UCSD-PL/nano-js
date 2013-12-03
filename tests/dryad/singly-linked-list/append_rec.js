//import "singly-linked-list.js"

// In below, separation between x and v in output IS obvious.
/* append_desired:: forall A l m.
     (x1:<l>+null,x2:<m>+null)/l |-> list[A] * m |-> list[A]
        => exists k. {v:<k>+null | (lenp(k) = lenp(x1) + lenp(x2)) && ((v = null) <=> ((x1 = null) && (x2 = null)))}
                     /k |-> list[A] */

/* heap measure lenp(x:<l>)  := len(*x) */
/* heap measure lenp(x:null) := 0       */

/* append:: forall A. (x1:<l>+null,x2:<m>+null)/l |-> xs:list[A] * m |-> ys:list[A]
                                  => {v:<k>+null | (((x1 != null) || (x2 != null)) <=> (v != null))}
                                     /k |-> zs:{list[A] | (if (x1 != null) 
                                                           then (if (x2 != null)
                                                                 then ((len(v) = len(xs) + len(ys)) && (keys(v) = Set_cup(keys(xs), keys(ys))))
                                                                 else ((len(v) = len(xs)) && (keys(v) = keys(xs))))
                                                           else (if (x2 != null)
                                                                 then ((len(v) = len(ys)) && (keys(v) = keys(ys)))
                                                                 else true))}
*/
/*@ append:: forall A. (x1:<l>+null,x2:<m>+null)/l |-> xs:list[A] * m |-> ys:list[A]
                                  => {v:<k>+null | ((((x1 != null) || (x2 != null)) <=> (v != null))
                                                    && (lenp(v,zs) = lenp(x1,xs) + lenp(x2,ys)))}
                                     /k |-> zs:list[A]
*/
function append(x1, x2){
  if (x1 != null){
      var n = x1.next;
      x1.next = append(n, x2);
      return x1;
  } else {
      return x2;
  } 
}
