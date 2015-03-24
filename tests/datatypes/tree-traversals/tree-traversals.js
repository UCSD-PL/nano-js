/*@ measure order :: forall A. (tree[A])      => number */
/*@ measure size  :: forall A. (tree[A]) => number */
/*@ measure lsize  :: forall A. (tree[A]) => number */
/*@ measure rsize  :: forall A. (tree[A]) => number */

/*@ measure preorderTree :: forall A. (x:tree[A]) => number */
/*@ measure inorderTree :: forall A. (x:tree[A]) => number */
/*@ measure postorderTree :: forall A. (x:tree[A]) => number */

/*@ type tree[A]
      exists! l |-> lt:tree[A] * r |-> rt:tree[A].
              t:{ key: A, left:{v:<l>+null | (Prop(nil(v)) => Prop(nil(lt)))}, right:{v:<r>+null | (Prop(nil(v)) => Prop(nil(rt)))}}

      with order(x) = (if (Prop(nil(x))) then 0 else (field_int(t, "key")))                    
      and   size(x) = (if (Prop(nil(x))) then 0 else (1 + size(lt) + size(rt)))
      and   lsize(x) = (if (Prop(nil(x))) then 0 else size(lt))
      and   rsize(x) = (if (Prop(nil(x))) then 0 else size(lt))
      and preorderTree(x) = (if (Prop(nil(x))) then 1 else 
                            (if ((preorderTree(rt) = 1) && (preorderTree(lt) = 1) && (Prop(nil(lt)) || (order(lt) = (field_int t "key") + 1)) && (Prop(nil(rt)) || (order(rt) = (field_int t "key") + 1 + size(lt)))) then 1 else 0))
                            
     and inorderTree(v) = (if (Prop(nil(x))) then 1 else 
                            (if (Prop(nil(lt))) then
                              (if (Prop(nil(rt))) then 1 else (if ((inorderTree(rt) = 1) && ((order rt) = (field_int t "key") + lsize(rt) + 1)) then 1 else 0))
                           else 
                           (if (Prop(nil(rt))) then
                               (if ((inorderTree(lt) = 1) && (order(lt) + rsize(lt) + 1 = (field_int t "key")))  then 1 else 0)
                           else (if ((inorderTree(lt) = 1) && (inorderTree(rt) = 1) && (order(lt) + rsize(lt) + 1 = (field_int t "key"))) then 1 else 0))))
                           
    and postorderTree(v) = (if (Prop(nil(x))) then 1 else
                            (if (Prop(nil(lt))) then 
                              (if (Prop(nil(rt))) then 1 else 
                                (if ((postorderTree(rt) = 1) && ((order(rt) + 1 = (field_int t "key")))) then 1 else 0)) else
                              (if (Prop(nil(rt))) then (if ((postorderTree(lt) = 1)  && ((order(lt) + 1 = (field_int t "key")))) then 1 else 0) else
                                (if ((postorderTree(lt) = 1) && (postorderTree(rt) = 1) && (order(lt) + 1 + size(rt) = (field_int t "key")) && (order(rt) + 1 = (field_int t "key"))) then 1 else 0))))
*/

/*@ invariant {v:tree[A] | ((Prop(nil(v)) => ((size(v) = 0) && (postorderTree(v) = 1) && (preorderTree(v) = 1) && (inorderTree(v) = 1))) && ((~(Prop(nil(v)))) => (size(v) = lsize(v) + rsize(v) + 1)))} */
        
         
      // and postorderTree(x) = 
      // (if (field_Ref t "left") = null then
      //   (if (field_Ref t "right") = null then 1 else (if ((postorderTree(rt) = 1) && (order(rt) + 1 = (field_int t "key"))) then 1 else 0))
      // else (if (field_Ref t "right") = null then
      //     (if ((postorderTree(lt) = 1) && (order(lt) + 1 = (field_int t "key"))) then 1 else 0)
      //   else (if (postorderTree(lt) = 1 && postorderTree(rt) = 1 && (order(lt) + 1 + size(rt) = (field_int t "key") ) && (order(rt) + 1 = (field_int t "key"))) then 1 else 0)))
      // (if (field_Ref t "left") = null then
      //   (if (field_Ref t "right") = null then 1 else (if ((preorderTree(rt) = 1) && (order(rt) = (field_int t "key") + 1)) then 1 else 0))
      // else (if (field_Ref t "right") = null then
      //     (if ((preorderTree(lt) = 1) && (order(lt) = (field_int t "key") + 1)) then 1 else 0)
      //   else (if (preorderTree(lt) = 1 && preorderTree(rt) = 1 && (order(lt) = (field_int t "key") + 1) && (order(rt) = (field_int t "key") + 1 + size(lt))) then 1 else 0)))
