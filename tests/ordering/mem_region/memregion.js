/*@ measure r_next :: forall S P. (x:dlist[S,P]) => boolean */
/*@ measure r_prev :: forall S P. (x:dlist[S,P]) => boolean */

/*@
  type dlist[S,P] exists! 
     l |-> tl:dlist[<l>, S].
     me:{ file_off:number
        , file_size:number
        , start_addr:number
        , size:number
        , next:<l>+null
        , prev:P }

    with r_next(x) = (if field_Ref(me,"next") = null then 0 else 1)
    and  r_prev(x) = (if field_Ref(me,"prev") = null then 0 else 1)
*/
