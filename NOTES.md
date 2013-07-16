

TODO
----

* Does `null` become cleaner with explicit unions?
    
      - T1 + T2
      
      G |- T2 <: Bot
      __________________ [Sub-Union]

      G |- T1 + T2 <: T1     


* Function App

* Infer Fold/Unfolc

* Clarify Issue with dependent field binders. At unfold
    - Add name binders for all fields
    - Replace record fields with singletons over names



Types
-----

B :=  int 
    | bool 
    | A

T := { v:B     | p }            // Base types
   | { v:R     | p }            // Records
   | { v:c[A..]| p }            // Pure TyConApp -- MAY BE NULL -- unless "p" indicates otherwise
   | { v:<l>   | p }            // Reference
   | (x1 : T1,...,xn:Tn) => T   // 1st Order Function types

R := Ø
   | f:T, R 

C := data c = forall A*, D      // TyCon-Def

D := ∃!H. {R}                   // TyCon-Body


Terms
-----

E := x                          // Variables
   | c                          // Constants 0, 1, +, -, true...
   | f(x1,...,xn)               // Function Call 
   | null
   | x.f                        // Field Read
   | {x with f = e}             // Field Update 


S := skip                        
   | x = e 
   | s1; s2
   | if [$\phi$] (e) { s1 } else { s2 }
   | return x
   
   | unfold x
   | fold x

   | x  = new e                 // Deref Create 
   | y  = !x                    // Deref Read
   | x := e                     // Deref Write

$\phi$ := x1:T1 ... xn:Tn

F := function f(x1...xn){s}     // Function Definition

P := F1:T1, ... Fn:Tn           // List of function definitions

G := Ø                          // Environments
   | x:T, G                      

H := emp                        // Heaps
   | (l |-> T) * h



Field Write
-----------

    x.f = e     IS      z =  x.f; x := {z with f = e}


Field Read
----------

    y = x.f     IS      y = x.f


Subtyping
---------

TODO

Well Formedness
---------------

TODO

Expression Typing
-----------------

TODO

Statement Typing
----------------

TODO






------------------------------------------------------------------------------------
PURE Record Read and Write 
------------------------------------------------------------------------------------

G |- x : {v:{f:T...} | v /= null}
___________________________________ [T-Fld-Read]

G |- x.f : T 



G |- e : T'

G |- x : {v:{R} | v /= null}
______________________________________________ [T-Fld-Read]

G |- x with f = e : {v: {R+f:T'} | v /= null}


------------------------------------------------------------------------------------
PURE Unfold and Fold
------------------------------------------------------------------------------------


G |- x : {v:c[T*] | v /= null}        c = \A*. {R} 
____________________________________________________ [T-Unfold]

G |- unfold x : G[x:{v:{R[T*/A*]} | v /= null}]



G |- x : {v: {R[T*/A*]} | v /= null}    c = \A*. {R} 
____________________________________________________ [T-Fold]

G |- fold x : G[x: {v:c[T*] | v /= null}]



------------------------------------------------------------------------------------
REFERENCE Create, Read and Write 
------------------------------------------------------------------------------------


G   |- e : T
_________________________________________________________

G/H |- x = new e : G[x:{v:<l> | v /= null}], H * l |-> T 


G |- x : {v:<l> | v /= null} 
______________________________________________ [T-Ptr-Read]

G / l |-> T * H |- (y = !x) : G, y:T / same



G |- x : {v:<l> | v /= null} 

G |- e : T'
______________________________________________ [T-Ptr-Write]

G / l |-> T * H |- x := e   : G / l |-> T' * H


------------------------------------------------------------------------------------
REFERENCE Unfold and Fold
------------------------------------------------------------------------------------


G |- x : {v:<l> | v /= null}        unwind(cd[T*], H', T')
____________________________________________________________[T-Unfold]

G / (l |-> c[T*]) * H |- unfold x : () / (l |-> T') * H' * H



G |- x : {v:<l> | v /= null}        unwind(cd[T*], H', T')
____________________________________________________________[T-Fold]

G / (l |-> T') * H' * H |- fold x : () / (l |-> c[T*] * H)



**unwind(D, H, T)**


______________________________ [Unwind-Emp]

unwind(G, ∃! emp . T, emp, T)



unwind(∃!hθ. T2 θ, h, T2')  
θ  = [l' / l]    
l' = fresh location
______________________________________________________ [Unwind-Bind]

unwind(G, ∃! l |-> T1 * h. T2,  (h * l' |-> T1'), T2')



// fresh                       :: D -> (H, T) 
// fresh(∃! l |-> T1 * h. T2)  = (h * l' |-> T1', T2') 
//   where 
//     (h, T2')                = fresh(∃!hθ. T2θ)
//     θ                       = [l' / l]
//     l'                      = fresh location
// 
// fresh(∃!emp. T)             = (emp, T)


------------------------------------------------------------------------------------
------------------------------------------------------------------------------------
------------------------------------------------------------------------------------

Examples
--------

    data list[A] = exists! (l' |-> list[A]) . { data : A
                                              , next : <l'> 
                                              }


0. Initialize


    /*@ mk1 :: forall A.(d:A) => list[A] */
    function mk1(d){
      var r  = {};
      r.data = d;
      r.next = null;
      return r;
    }

1. Collective Strong Update


    /*@ foo :: (xs:?list[v=0]<l>) => void/?list[v=1]<l> */ 
    
    function foo(xs){
      if (xs) {
        @unfold xs
        xs.data = 1;
        foo(xs.next)
        @fold xs
      }
      return;
    }

2. List Snoc

    // Adds 1 to length of xs
    function snoc(xs, d) {
      
    }

3. List Append


4. List Insert Order

+ Merge locations/SSA cleanly

+ Base Type System

    + Merge locations/SSA cleanly
    + First-class field names
    + Ad-hoc unions

+ Fancy Type System

    + Generalized Fold/Unfold
    + Measures
    + Abstract Refinements



Must Have Locations
-------------------

Yes.

Definitely need locations, weak and strong: if only to manage effects:
     
     function foo(x){

        x.a = x.a +1
     }

Somehow, have to record the fact that the "a" field is mutated. 

Don't want to get sucked into modifies-clause hell...


Fancy Folds
-----------

"htype" defines a proposition of the HEAP

    data list[A] 
      = ∃! l |-> list[A] . { data : A, next : <l> }


But where does l' live? Need a HEAP? 

Let `h` be htype (Heap Type), then define:


    ?h<l>   := emp              OR    l |-> (rhs h) @ l

    x:?h<l> := {v=NULL} / emp   OR    v:<l> / l |-> (rhs h) @ l


Can simplify above with some join algebra

    h1 + h2

    (t1 + t2) / (h1 + h2) = (t1/h1) + (t2/h2)

With this in mind, show that:

    /*@ foo :: (xs:?list[v=0]<l>) => void/?list[v=1]<l> */ 
    
    function foo(xs){
      if (xs) {
        @unfold xs
        xs.data = 1;
        foo(xs.next)
        @fold xs
      }
      return;
    }

What exact semantics for @unfold and @fold?


Deleting a List Element

    Source Level /*@ delete :: (list[A], A) => list[A] */
    
    System Level /*@ delete :: (<l>, A) / l |-> list[A] => <l1> / l1 |-> list[A] */

    function delete(xs, d){
      
      if (xs) { 
        var mydata = xs.data;
        
        if (mydata == d) { 
          return xs.next; 
        }
        
        xs.next  = delete(xs.next, d);
      }
      
      return xs;
    
    }


Insert (hassle: do we return a NEW location or the SAME location as root of list?)

    /*@ mk1 :: forall A.(d:A) => list[A] */
    function mk1(d){
      var r  = {};
      r.data = d;
      r.next = null;
      return r;
    }
  
    Source Level /*@ insert :: (list[A], A) => list[A] */
    
    System Level /*@ insert :: (<l>, A) / l |-> list[A] => <l1> / l1 |-> list[A] */

    function insert(xs, d){
      if (!xs) {
        return mk1(d);
      }
      
      if (d <= xs.data){
       var y  = mk1(d);
       y.next = xs;
       return y;
      }
   
      xs.next = insert(xs.next, d);
      
      return xs;
    }


Reversing a List

    function reverse(xs){
      return go(xs, null);
    }

    
    (xs:<l1>, ys:<l2>)/l1 |-> list[A] * l2 |-> list[A] => <l>/l |-> list[A]

    function rev(xs, ys){
                                xs:<l1>, ys:<l2> / emp 
      if (xs){
                                xs:<l1>, ys:<l2>, xs /= null / emp 

        //unfold l1/xs          xs:<l1>, ys:<l2>, xs /= null /   l1  |-> {data: A, next:<l1'>} 
                                                               * l1' |-> list[A]
                                                               * l2  |-> list[A]

        var tl  = xs.next;
                                xs:<l1>, ys:<l2>, xs /= null 
                                tl:<l1'>                     /   l1  |-> {data: A, next:<l1'>} 
                                                               * l1' |-> list[A]
                                                               * l2  |-> list[A]

        xs.next = ys;
                                xs:<l1>, ys:<l2>, xs /= null 
                                tl:<l1'>                     /   l1  |-> {data: A, next:<l2>} 
                                                               * l2  |-> list[A]
                                                               * l1' |-> list[A]

        //fold l1/xs
                                xs:<l1>, ys:<l2>, xs /= null 
                                tl:<l1'>                     /   l1  |-> list[A] 
                                                               * l1' |-> list[A]

        var z = go(tl, xs);

        return z
      
      }
      
      return ys;
    }
    
    
    
    
    
    (xs:<l1>, ys:<l2>)/l1 |-> list[A] * l2 |-> list[A] => <l>/l |-> list[A]
    
    function rev(xs, ys){
                                xs:<l1>, ys:<l2> / emp 
      
      var z0 = null;

      if [z3] (xs){
                                xs:<l1>, ys:<l2>, xs /= null /   l1  |-> list[A]
                                                               * l2  |-> list[A]

        //unfold l1/xs          xs:<l1>, ys:<l2>, xs /= null /   l1  |-> {data: A, next:<l1'>} 
                                                               * l1' |-> list[A]
                                                               * l2  |-> list[A]

        var tl  = xs.next;
                                xs:<l1>, ys:<l2>, xs /= null 
                                tl:<l1'>                     /   l1  |-> {data: A, next:<l1'>} 
                                                               * l1' |-> list[A]
                                                               * l2  |-> list[A]

        xs.next = ys;
                                xs:<l1>, ys:<l2>, xs /= null 
                                tl:<l1'>                     /   l1  |-> {data: A, next:<l2>} 
                                                               * l2  |-> list[A]
                                                               * l1' |-> list[A]

        //fold l1/xs
                                xs:<l1>, ys:<l2>, xs /= null 
                                tl:<l1'>                     /   l1  |-> list[A] 
                                                               * l1' |-> list[A]

        z1 = go(tl, xs);
                                xs:<l1>, ys:<l2>, xs /= null 
                                tl:<l1'>,z1:<l4>             /   l4  |-> list[A]
        
        //prune
                                z1:<l4>                      /   l4  |-> list[A]
        


      } else {
        
                                xs:<l1>, ys:<l2>, xs == null / 
                                                                 l1  |-> list[A]
                                                               * l2  |-> list[A]

        z2 = ys;
      
                                xs:<l1>, ys:<l2>, xs == null   
                                z2:<l2>                      /   l1  |-> list[A]
                                                               * l2  |-> list[A]

        // rename l2->l4
                                xs:<l1>, ys:<l4>, xs == null   
                                z2:<l4>                      /   l1  |-> list[A]
                                                               * l4  |-> list[A]


      } // join on z1,2

                                z3:<l4>                      /   l4 |->  list[A] 
            
      return z3;
    }





**Lessons**

1. _Unfold_ at use (i.e. field lookup)
2. _Fold_ at join or call (i.e. when you REQUIRE something folded up)
3. _Prune_ environment binders? Or just mark as dead?
4. Why are we unifying/renaming the l2 and l4 above? Whats the tip off? 
   - Is it `z`?
   - Is it the ONLY sensible remaining binder?





Doubly Linked Lists 
-------------------

    data dll[A, B] 
      = ∃! l |-> dll[A,<l>] . 
           { data : A
           , next : <l>
           , prev : B 
           }


Parented Trees
--------------

    data tree[A, B] 
      = ∃! l1 |-> tree[A,<l1>]  
           l2 |-> tree[A,<l2>] .
           { data : A
           , left : <l1> 
           , right: <l2>
           , root : B
           }


--------------------------------------------------------------------------------
GIBBERISH:
--------------------------------------------------------------------------------

INVARIANT: the only explicit heap bindings are for locations BOUND TO VARIABLES

so assume


    xs:list[A]<lx>

until you bind

    ys = xs.next

You DONT need to put <ly> in the heap.

Code

    function foo(xs){
      if (xs) {
        xs.data = 1;
        foo(xs.next)
      }
      return;
    }

Programmer writes

    foo :: (x:?list[v=0]) => void

System reads

    foo :: (x:?<lx>)/list[v=0]<lx> => void/list[v=1]<lx>












