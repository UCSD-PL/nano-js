/*@ measure keys :: forall A. (tree[A]) => set[number]  */

/*@ 
type tree[A] < p :: (A, A) => prop, q :: (A, A) => prop >
     exists!   l |-> sls:tree[A<p (field_int me "data")>]<p,q>
             * r |-> srs:tree[A<q (field_int me "data")>]<p,q>
              . me:{ data: A, left:<l>+null, right:<r>+null } 

       keys(null) = Set_cap(Set_sng(0),Set_sng(1))
       keys(x)    = Set_sng(field_int(me, "data")) ∪ keys(sls) ∪ keys(srs)         
*/

/*
  1. from type defs (v [< = >] field...)
  2. from measures (m(x) = m(y))
*/

/*@ qualif KeysEqThinger(v:T,x:Rec): (~Set_mem(field_int(x,"data"),keys(v))) */
/*@ qualif KeysEqThinger(v:T,x:number): (~Set_mem(x,keys(v))) */
/*@ qualif KeysEqThinger(v:T,x:T,y:T): (keys(v) = Set_cup(keys(x),keys(y))) */
/*@ qualif RootInput(v:int, x:Rec): v < field_int(x, "data") */
/*@ qualif RootInput(v:int, x:Rec): v > field_int(x, "data") */
