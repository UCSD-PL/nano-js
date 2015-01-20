/*@ measure order :: (tree[A])      => A */
/*@ measure size  :: forall A. (tree[A]) => number */
/*@ measure sizep :: forall A. (<l>+null, tree[A]) => number */
/*@ measure sizep(p,x) = (if (p = null) then 0 else size(x)) */ 
/*@ measure rsize  :: forall A. (tree[A])           => number */
/*@ measure lsize  :: forall A. (tree[A])           => number *///32

/*@ measure preorderTree :: forall A. (x:tree[A]) => number */
/*@ measure inorderTree :: forall A. (x:tree[A]) => number */
/*@ measure postorderTree :: forall A. (x:tree[A]) => number */

/*@ type tree[A]
      exists! l |-> lt:tree[A] * r |-> rt:tree[A].
              t:{ key: A, left:<l>+null, right:<r>+null}

      with order(x) = field_int(t, "key")                    
      and   size(x) = (1 + lsize(x) + rsize(x))
      and  lsize(x) = (if (field_Ref t "left") = null then 0 else size(lt))
      and  rsize(x) = (if (field_Ref t "right") = null then 0 else size(rt))

      and preorderTree(x) = 
      (if (field_Ref t "left") = null then
        (if (field_Ref t "right") = null then 1 else (if ((preorderTree(rt) = 1) && (order(rt) = (field_int t "key") + 1)) then 1 else 0))
      else (if (field_Ref t "right") = null then
          (if ((preorderTree(lt) = 1) && (order(lt) = (field_int t "key") + 1)) then 1 else 0)
        else (if (preorderTree(lt) = 1 && preorderTree(rt) = 1 && (order(lt) = (field_int t "key") + 1) && (order(rt) = (field_int t "key") + 1 + size(lt))) then 1 else 0)))
        
      and inorderTree(x) = 
      (if (field_Ref t "left") = null then
        (if (field_Ref t "right") = null then 1 else (if ((inorderTree(rt) = 1) && (order(rt) = (field_int t "key") + lsize(rt) + 1)) then 1 else 0))
        else (if (field_Ref t "right") = null then
          (if ((order(lt) + rsize(lt) + 1 = (field_int t "key")) && (inorderTree(lt) = 1)) then 1 else 0)
         else (if (inorderTree(lt) = 1 && inorderTree(rt) = 1 && 
         (order(lt) + rsize(lt) + 1 = (field_int t "key")) && (order(lt) + rsize(lt) + 1 = (field_int t "key"))) then 1 else 0)))
         
      and postorderTree(x) = 
      (if (field_Ref t "left") = null then
        (if (field_Ref t "right") = null then 1 else (if ((postorderTree(rt) = 1) && (order(rt) + 1 = (field_int t "key"))) then 1 else 0))
      else (if (field_Ref t "right") = null then
          (if ((postorderTree(lt) = 1) && (order(lt) + 1 = (field_int t "key"))) then 1 else 0)
        else (if (postorderTree(lt) = 1 && postorderTree(rt) = 1 && (order(lt) + 1 + size(rt) = (field_int t "key") ) && (order(rt) + 1 = (field_int t "key"))) then 1 else 0)))
         
      
        
*/
