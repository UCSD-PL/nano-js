README
=======

Language for experimenting with verification algorithms

nano-js is the basis for the programming assignments in 

    http://goto.ucsd.edu/~rjhala/classes/sp13/cse291

Dependencies
------------

* git clone git@github.com:ucsd-progsys/liquid-fixpoint.git 
* git clone git@github.com:UCSD-PL/language-ecmascript.git
* nano-js


TODO
----
 
Homework Plan
-------------

HW 1
1a. VCG 
1b. Use ESC/J

HW 2
2a. ConsGen = VCG+K for LoopInv via FIXPOINT    [Easy]
    -> Hmm...
2b. Implement FIXPOINT (over liquid-fixpoint)   [Hard]
    -> Hmm...
    

HW 3
3a. VCG for Refinement Type Checking            [Hard]
3b. Consgen = VCG+K for Liquid Inference via FIXPOINT


(Refinement) Types for Nano-JS
------------------------------

HW 2

0. K-Constraint Generation for Pre/Post/Loops

HW 3

run: make test to see what to do next.

0. Type Types 
1. Parse Types 
2. Vanilla Type Checker     
    - Basic Int/Bool/Expr {------------------------ HEREHEREHEREHERE
            >> HOW TO GET RETURNVAR? Parameterized by env YUCK. Put into TCM?

            
    - First-order Funs
    - Higher-Order Funs 
    - Polymorphism
    - Records

3. Passifier [SSA-Transformation] 


4. Parse Refinement Types
5. Refinement Type Checker      [HW]
6. Liquid Constraint Generation [HW]

tests/typed/pos/*.js

    higher-order
        twice.js
        while.js
        loop.js
        foldn.js

    lists
        map.js
        fold.js
        listsum.js

    measure
        kmeans.js

    measures: 

        cons :: forall A. (x:A, xs:List A) -> {v: List A | (len v) = 1 + (len xs)}
        nil  :: forall A. () -> {v: List A | (len v) = 0}
        head :: forall A. (xs:{v: List A | 0 < (len v)}) -> A 
        tail :: forall A. (xs:{v: List A | 0 < (len v)}) -> {v: List A | (len v) = (len xs) - 1 }
        null :: forall A. (xs:List A) -> {v: Bool | (Prop v) <=> ((len v) = 0) }




---------------------------------------------------------------------------------------


Base Types
----------

B := Int

Records
-------

N := \[a] -> { x:T.. }

Types
-----

S := \[A..].T

T := B
   | a
   | (Ti..) -> T
   | N [T..]

    TyVars(T) \subseteq \cup_i TyVars(Ti)
    -------------------------------------
              |- (xi:Ti..) -> T


Expressions
-----------

e := x                          -- var
   | c                          -- int const
   | e `o` e                    -- int op
   | e `r` e                    -- int rel
   | e `b` e                    -- bool op 
   | e (e..)                    -- Function Call 
   | {x:e..}                    -- Object Literal
   | x.f                        -- Field Read
   | function f(xi..){c} :: S

Commands
--------

c := x = e          -- assignment
   | c; c           -- sequence
   | if e c1 c2     -- if-then-else
   | while e c      -- while-loop [NUKE]
   | return e       -- return
   | x.f = e        -- x := {x with f = e}


Programs
--------

p := (f::S)..


Typing Environments
-------------------

G := 0 | G, x:T 


Typing Rules 
------------

**Expressions** [G |- e => t]

---------------
G |- x => (G x)

-------------
G |- c => Int

G |- e1 => Int G |- e2 => Int
-----------------------------
G |- e1 `o` e2 => Int

G |- e1 => Int G |- e2 => Int
-----------------------------
G |- e1 `r` e2 => Bool

G |- e1 => Bool G |- e2 => Bool 
-------------------------------
G |- e1 `b` e2 => Bool


N = \[A..] -> {fi:Ti...}    
G |- ei => Ti'  
unify(Ti.., Ti'..) = θ 
--------------------------------
G |- {fi:ei} => N [0 A]


G(x) = N [T..]   F(N) = \[A..] -> {f:Tf}
----------------------------------------
G |- x.f => Tf[T../A..]

G |- e  => \[A].(Ti) -> T    
G |- ei => Ti'  
unify(Ti.., Ti'..) = θ 
-----------------------------------
G |- e (ei..) => θ T 

**Commands** [G |- c => G' + EXIT]

G |- e => T
--------------------
G |- x = e => G, x:T

G |- c1 => EXIT
-----------------------
G |- c1; c2 => EXIT 

G |- c1 => G1       G1 not EXIT      G1 |- c2 => G2
---------------------------------------------------
G |- c1; c2 => G2

G |- e  => Bool     G |- c1 => G1   G |- c2 => G2
--------------------------------------------------
G |- if e c1 c2 => G1 `join` G2

G |- e => Bool      G |- c => G'
---------------------------------
G |- while e c => G `join` G'

G |- e => T   T = G($result) 
----------------------------
G |- return e => EXIT

G(x) = N [T..]      F(N) = \[A..] -> {f:Tf}     G |- e => Tf[T../A..]
----------------------------------------------------------------------
G |- (x.f = e) => G 

**Functions** [G |- function f...]

S  = forall a...(Ti..) -> T
G' = G, a.., xi:Ti.., $result:T
G' |- c => EXIT
-----------------------------------
G |- function f(xi..){c} :: S => S 

**Programs** [ |- (f::S).. ]

G = (fi::Si)..    foreach i. G |- fi::Si : Si 
----------------------------------------------
|- (fi::Si)..

where 

join G1 G2             = [x:T | x:T in G1 and x:T in G2] 
join EXIT(_) G         = G
join G EXIT(_)         = G
join (EXIT T) (EXIT T) = Bot T

---------------------------------------------------------------------

How to modify for Refinement Types?

0. [SKIP WHILE]

1. Explicit JOIN for types (uses MEET for CONTRA)

2. CHECK Subtyping at function call? [CHECK]

3. CHECK Subtyping at return? [CHECK]

1. [NO] Mark certain assignments as SSA
   Induce Subtyping Constraints there

2. LOOP CHECK? [NO WHILE?]

