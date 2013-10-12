// Short form
/*@ type tree[A]<P :: A->A->Prop> <Q :: A->A->Prop> 
      = { data  : A
        , left  : ?tree[A<P data>]<P, Q>
        , right : ?tree[A<Q data>]<P, Q>
        }
 */

// Expands to
/*@ type tree[A]<P :: A -> A -> Prop> <Q :: A -> A -> Prop> = 
      exists! l |-> tree[{v:A | (P data v)}]<P, Q>
            * r |-> tree[{v:A | (Q data v)}]<P, Q>
            . { data : A, left : ?<l>, right: ?<r> }
 */

/*@ type bst[A] = tree[A]<{\x y -> x < y}, {\x y -> x >y}> */

/*@ measure keys :: (<l> + null) / l |-> tree[A] => set[A] 
  measure keys(x) {
    | (x :: null) => set_empty
    | (x :: <l> ) => set_cup(set_singleton(x.data), set_cup(keys(x.left), keys(x.right)));
  }
*/

/*@ measure root :: (<l>) / l |-> tree[A] => A 
  measure keys(x) {
    | (x :: <l> ) => x.data 
  }
*/
