// type list[A] = exists! l |-> list[A]. {  data : A, next : <l> + null }

/*@ measure len :: (?<l>)/l |-> list[A] => number
  measure len(x) {
    | (x :: null) => 0 
    | (x :: <l> ) => 1 + len(x.next) 
  }
*/

/*@ measure keys :: (<l> + null) / l |-> list[A] => set[A] 
  measure keys(x) {
    | (x :: null) => set_empty
    | (x :: <l> ) => set_cup(set_singleton(x.data), keys(x.next));
  }
*/

// predicate SetPlus(X,Y,Z) = X == set_cup(Y, set_singleton(Z))
