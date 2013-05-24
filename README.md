README
=======

Language for experimenting with verification algorithms

nano-js is the basis for the programming assignments in 

    http://goto.ucsd.edu/~rjhala/classes/sp13/cse291

Dependencies
------------

* cabal update
* cabal install language-ecmascript 
* git clone git@github.com:ucsd-progsys/liquid-fixpoint.git 
* git clone git@github.com:ucsd-pl/nano-js.git 
* cd nano-js
* make

* git clone git@github.com:UCSD-PL/language-ecmascript.git
HW 2 Release Checklist
----------------------

* dumpInferredTypes

* Update GOTO haddocks
    
    - liquid-fixpoint
    - nano-js [generate from algo-verif-repo]
 
* Copy over to algo-verif repo
    
    - ADD README with hints
        
        use `tracePP`
        
        See lecture notes: https://github.com/UCSD-PL/algorithmic-software-verification/blob/master/web/slides/lec-refinement-types-3.markdown
        
        You are essentially implementing the typing rules shown there.

        step 1. fresh* return types with templates
        step 2. "typechecking" as in Liquid/Liquid.hs will generate constraints over templates
        step 3. these are solved by "fixpoint"

        verifyFile f   = reftypeCheck f . typeCheck . ssaTransform =<< parseNanoFromFile f
        reftypeCheck f = solveConstraints f . generateConstraints  
        
        You only implement "step 2" 
        
            > Only need to fill in code in Language/Nano/Liquid/Liquid.hs

            > See "HINTS" to see how to get fresh templates for unknown types for 
                + phi-vars                  (`freshTyPhis`)
                + function signatures       (`freshTyFun`)
                + polymorphic instantiation (`freshTyInst`)

            Debugging will be **HARD**: use `tracePP` and related functions aggressively.

            1. modify envAdds    to log the types/template
            
            2. modify subType/s  to see EXACTLY what constraints are being added at each site.
            
            3. stare at .fq files to see what the generated constraints look like.
            
            4. use the `ssaTransform'` (instead of `ssaTransform`) if you
               want to see the output SSA.
            
            5. the recorded templates and constraints for each binder will be saved 
               in `foo.js.annot`. look at it to make sure the right templates/types 
               are being inferred.
            
            6. for several benchmarks, you will need to write EXTRA
               QUALIFIERS (predicates) from which the right types can be
               inferred.

               see:
                    tests/liquid/pos/inc.js
                    tests/liquid/pos/cousot.js
               
               for examples. And see:

                    include/prelude.js

               for a list of "default library" qualifiers. You can DELETE
               all the qualifiers (or just remove the "@") to see the exact
               set needed for each program.

             7. Figuring out the extra qualifiers may be the hardest part of
                the assignment. Or not. When in doubt, put in EXPLICIT 
                refinement type signatures, corresponding to how you think
                each function should behave...

* RELEASE

Homework Plan
-------------

HW 1
1a. VCG 
1b. Use ESC/J

HW 2
2a. ConsGen = VCG+K for LoopInv via FIXPOINT    [Easy]
2b. Implement FIXPOINT (over liquid-fixpoint)   [Hard]

HW 3
3a. VCG for Refinement Type Checking            [Hard]
3b. Consgen = VCG+K for Liquid Inference via FIXPOINT

MAJOR REMAINING FEATURES
------------------------

    + HTML annot
    - Scrape Qualifiers
    - unions
    - Records

Tests
-----

    DOTPROD?
    KMP?
    mapreduce?
    kmeans?

Include
-------

/*@ include "path/to/foo.js" */
  >> add to "Spec"
  >> update parser
  >> recursively traverse all files
          traverseFiles :: (FilePath -> IO [FilePath]) -> FilePath -> IO [FilePath]

HashMap.Strict Container MADNESS
--------------------------------

    tests/liquid/pos/minindex01.js

grumble about "unbound variable" (due to missing key in envFindTy)

    sometimes it works with "forloop" sometimes doesn't!
    when it doesn't if you change the name to "forLoop" or
    "humphreyAppleby" it works fine!

    using: 
        ~/research/liquid/hsenv
        hashable-1.2.0.7

    you get the error in:
        tests/liquid/pos/locks-cond.js

