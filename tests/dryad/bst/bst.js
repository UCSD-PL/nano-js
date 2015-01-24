/*@ measure keys :: forall A. (tree[A]) => set[number]  */
/* measure keysp :: forall A. (<l> + null, tree[A]) => set[number]  */
/* measure keysp(p,x) = (if (p = null) then Set_sng(1) ∩ Set_sng(0) else keys(x)) */

/* type bst[A] = tree[A]<\h v -> h < v><\h v -> h > v>
/*@ type tree[A] < p :: (A, A) => prop, q :: (A, A) => prop >
      exists!   l |-> sls:tree[A<p data>]<p,q>
              * r |-> srs:tree[A<q data>]<p,q>
              . me:{ data: A, left:{v:<l>+null | (Prop(nil(v)) => Prop(nil(sls)))}, right:{v:<r>+null | (Prop(nil(v)) => Prop(nil(srs)))} } 

       with keys(x) =   Set_sng(field_int(me, "data")) ∪ keys(sls) ∪ keys(srs)          */

/*
  1. from type defs (v [< = >] field...)
  2. from measures (m(x) = m(y))
*/

/*@ invariant {v:tree[A] | (Prop(nil(v)) => (keys(v) = Set_cap(Set_sng(0),Set_sng(1))))} */
