
// type list[A] = exists! l |-> list[A]. {  data : A, next : <l> + null }

// probably not very usable...

/*@ measure keys :: (<l> + null) / l |-> list[A] => set[A] 
    function keys(x){  
      if (x == null) {
         return set_empty;
      } else {
         return 
         set_cup(set_singleton(x.data), keys(x.next));
      }
    }
 */

/*@ measure len :: (?<l>)/l |-> dlist[A, B] => number
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
