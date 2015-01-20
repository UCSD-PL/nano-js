/*@ measure keys :: forall A. (tree[A]) => set[number]  */
/*@ measure keysp :: forall A. (<l> + null, tree[A]) => set[number]  */
/*@ measure keysp(p,x) = (if (p = null) then Set_sng(1) ∩ Set_sng(0) else keys(x)) */

/* type bst[A] = tree[A]<\h v -> h < v><\h v -> h > v>
/*@ type tree[A] < p :: (A, A) => prop, q :: (A, A) => prop >
      exists!   l |-> sls:tree[A<p data>]<p,q>
              * r |-> srs:tree[A<q data>]<p,q>
              . me:{ data: A, left:<l>+null, right:<r>+null } 

       with keys(x) =   Set_sng(field_int(me, "data"))
                     ∪ keysp(field_Ref(me, "left"), sls)
                     ∪ keysp(field_Ref(me, "right"), srs)          */
