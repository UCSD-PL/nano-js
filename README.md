README
=======

Language for experimenting with verification algorithms

nano-js is the basis for the programming assignments in 

    http://goto.ucsd.edu/~rjhala/classes/sp13/cse291

Dependencies
------------

* git clone git@github.com:ucsd-progsys/liquid-fixpoint.git 
* nano-js
   

MAJOR REMAINING FEATURES
------------------------

    + HTML annot
    - Scrape Qualifiers
    - unions
    - Records
    - VCG + K for ESC
    - IMPLEMENT Fixpoint in Haskell


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

