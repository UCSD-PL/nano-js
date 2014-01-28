/*@ measure order :: (tree[A])      => A */

/*@ measure size  :: forall A. (tree[A]) => number */
/*@ measure sizep :: forall A. (<l>+null, tree[A]) => number */
/*@ measure sizep(p,x) = (if (p = null) then 0 else size(x)) */

/*@ measure rsize  :: forall A. (tree[A])           => number */
/* measure rsizep :: forall A. (<l>+null, tree[A]) => number */
/* measure rsizep(p,x) = (if (p = null) then 0 else rsize(x)) */

/*@ measure lsize  :: forall A. (tree[A])           => number */
/* measure lsizep :: forall A. (<l>+null, tree[A]) => number */
/* measure lsizep(p,x) = (if (p = null) then 0 else lsize(x)) */

/*@ type tree[A] < p :: (<l>,tree[A],<r>,tree[A],A) => prop, q :: (<l>,tree[A],<r>,tree[A],A) => prop>
      exists! l |-> lt:tree[A]<p,q> * r |-> rt:tree[A]<p,q>.
              t:{ key: A<p (field t "left") lt (field t "right") rt, 
                         q (field t "left") lt (field t "right") rt>, left:<l>+null, right:<r>+null}

      with order(x) = field(t, "key")                    
      and   size(x) = (1 + lsize(x) + rsize(x))
      and  lsize(x) = (if (field t "left") = null then 0 else size(lt))
      and  rsize(x) = (if (field t "right") = null then 0 else size(rt))
*/
