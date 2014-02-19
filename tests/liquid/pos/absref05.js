/*@ type list[A]<p :: (A, A) => prop>
        exists! l |-> tl:list[A<p (field r "data")>]<p>. 
          r:{ data : A, next : <l>+null } */

/*@ consSorted ::
  (p:<p>, k:{v:number | true})/p |-> ps:list[number]<{\h v -> h <= v}>
   => <l>/l |-> ls:list[number]<{\h v -> h <= v}>*/
function consSorted(p,k) {
  d = p.data;   //   l |-> hd:{ data: number, next :<1> }
                // * 1 |-> tl:list[number<p field(hd,data)>]<p>

  if (k <= d) {
  //guard:{v:bool | k < field(hd, "data")} 
    var y = {};
    y.data = k;
    y.next = p;
    return y;
  } else {
    return p;
  }
}
  
