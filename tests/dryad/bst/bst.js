/*@ measure keys :: forall A. (tree[A]) => set[number]  */
/* measure keysp :: forall A. (<l> + null, tree[A]) => set[number]  */
/* measure keysp(p,x) = (if (p = null) then Set_sng(1) ∩ Set_sng(0) else keys(x)) */

/* type bst[A] = tree[A]<\h v -> h < v><\h v -> h > v>
/*@ type tree[A] < p :: (A, A) => prop, q :: (A, A) => prop >
      exists!   l |-> sls:tree[A<p (field_int me "data")>]<p,q>
              * r |-> srs:tree[A<q (field_int me "data")>]<p,q>
              . me:{ data: A, left:{v:<l>+null | (Prop(nil(v)) => Prop(nil(sls)))}, right:{v:<r>+null | (Prop(nil(v)) => Prop(nil(srs)))} } 

       with keys(x) =   Set_sng(field_int(me, "data")) ∪ keys(sls) ∪ keys(srs)          */

/*
  1. from type defs (v [< = >] field...)
  2. from measures (m(x) = m(y))
*/

/*@ invariant {v:tree[A] | (Prop(nil(v)) => (keys(v) = Set_cap(Set_sng(0),Set_sng(1))))} */

/*@ qualif KeysEqThinger(v:T,x:Rec): (~Set_mem(field_int(x,"data"),keys(v))) */
/*@ qualif KeysEqThinger(v:T,x:a): (~Set_mem(x,keys(v))) */
/*@ qualif KeysEqThing(v:T,x:T): keys(x) = keys(v) */
/*@ qualif RootInput(v:int, x:Rec): v < field_int(x, "data") */
/*@ qualif RootInput(v:int, x:Rec): v > field_int(x, "data") */
