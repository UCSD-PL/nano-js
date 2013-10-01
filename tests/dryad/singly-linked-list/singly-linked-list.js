/*@ measure keys :: (<l> + null) / l |-> list[A] => set[A] 
    function keys(x){  
      if (x == null) {
         return set_empty;
      } else {
         return set_cup(set_singleton(x.data), keys(x.next));
      }
    }
 */
