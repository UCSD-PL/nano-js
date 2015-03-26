/*@ type either[A,B] A + B     */

/*@ measure keys :: forall A. (clist[A]) => set[number]  */
/*@ measure len  :: forall A. (clist[A]) => number  */

/*@ isL   :: forall A B. (x:{v:either[A,B] | true}) => {v:boolean | (if Prop(v) then
                                                                     (ttag(x) = "inl")
                                                                  else
                                                                     (ttag(x) = "inr"))}          */

/*@ projL :: forall A B. ({v:either[A,B] | (ttag(v) = "inl")}) => A                                 */
/*@ projR :: forall A B. ({v:either[A,B] | (ttag(v) = "inr")}) => B                                 */
/*@ inL   :: forall A B. (A) => {v:either[A,B] | (ttag(v) = "inl")}                                 */
/*@ inR   :: forall A B. (B) => {v:either[A,B] | (ttag(v) = "inr")}                                 */

/*@
  type clist[A,H] exists! l |-> rest:clist[A,H]
                        . me:{data:A, next:either[<l>,H]}

       with keys(x) = (if (ttag(field_T(me, "next")) = "inl") then
                           Set_cup(Set_sng(field_int(me, "data")), keys(rest))
                        else
                           Set_sng(field_int(me, "data")))

       and len(x) = (if (ttag(field_T(me, "next")) = "inl")
                          then (1 + len(rest))
                          else 1)
*/

// A vanilla circular list would have type.
//    hd :: clist[A, {v:<hd> | v = hd}]

// NOTE: we need to implicitly strengthen <l> to include 
// 1. the equality     v  = l
// 2. the disequality  v /= l' for all other l' in scope.
