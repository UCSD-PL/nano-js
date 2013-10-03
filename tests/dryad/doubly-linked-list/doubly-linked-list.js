/*@ type dlist[A, Self] = exists! l |-> dlist[A, <l>]. { data : A
                                                       , next : ?<l> 
                                                       , prev : Self 
                                                       }
 */

/*@ type rdlist[A, Self] = exists! l |-> rdlist[A, <l>]. { data : A
                                                         , next : Self 
                                                         , prev : ?<l> 
                                                         }
 */

/*@ measure len :: (?<l>)/l |-> dlist[A, B] => number
  measure len(x) {
    | (x :: null) => 0 
    | (x :: <l> ) => 1 + len(x.next) 
  }
*/

/*@ measure keys :: (?<l>)/l |-> dlist[A, B] => set[A] 
  measure keys(x) {
    | (x :: null) => set_empty
    | (x :: <l> ) => set_cup(set_singleton(x.data), keys(x.next));
  }
*/

/*@ measure rkeys :: (?<l>)/l |-> dlist[A, <l>] => set[A] 
  measure rkeys(x) {
    | (x :: null) => set_empty
    | (x :: <l> ) => set_cup(set_singleton(x.data), rkeys(x.prev));
  }
*/
