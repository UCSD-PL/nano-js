# Status

## heaps+locations

* I've added reference types and changed objects so
  that they live in the heap. That is, the expression 

    { foo: bar }

  evaluates to a reference to a new location, `l`, containing the object 

    {foo: bar}. 
    
  Currently, all locations are "0 or 1" locations.

* Type definitions may mention a quantified heap:

    /*@ type list[A] exists! (l |-> list[A]) . { data: A, next: <l>+null } */

* Location winding/unwinding

  Locations are unwound on demand. 
 
  All locations are wound up at the end of a basic block, i.e. at the end of the block
  of statements inside both `if` and `else` branches, and before `return` statements.
 
  TODO: Infer that *new* locations need to be wound up, i.e. in the program

    /*@ newList :: ()/emp => <l>/l |-> list[int] */
    function newList() {
      var x = {data:3, next: null};
      return x;
    }
    
  The typechecker should infer from the function's spec that `x` should be wound up
  into a `list`.
  
* Mutation 

  I still need to add mutation of objects. In preparation for this,
  however, I ran into the following, due to unions. In particular,
  I expect the type
  
      <l> + null
  
  will be common. Given a possibly null reference `x:<l>+null`, typechecking
  
      x.data
  
  may be tricky. I've just followed what is done in other cases, which
  is to insert a cast to a union containing only references.
