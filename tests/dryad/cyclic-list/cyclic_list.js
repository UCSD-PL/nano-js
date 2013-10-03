/*@ type clist[A, End] = exists! l |-> clist[A, End]. { data : A
                                                      , next : <l> + End 
                                                      }
 */

// A vanilla circular list would have type.
//    hd :: clist[A, {v:<hd> | v = hd}]

// NOTE: we need to implicitly strengthen <l> to include 
// 1. the equality     v  = l
// 2. the disequality  v /= l' for all other l' in scope.

