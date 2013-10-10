
/*@ type list[A]<P :: A -> A -> Prop> = 
       exists! l |-> list[{v:A| (P data v)}]<P>. { data : A, next : <l> + null }
 */

/*@ type incList[A] = list[A]<{\x y -> x <= y}> */

/*@ measure keys :: (<l> + null) / l |-> list[A] => set[A] 
  measure keys(x) {
    | (x :: null) => set_empty
    | (x :: <l> ) => set_cup(set_singleton(x.data), keys(x.next));
  }
*/

// predicate SetPlus(X,Y,Z) = X == set_cup(Y, set_singleton(Z))
