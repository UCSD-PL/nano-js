/*@ extern crash :: forall A.() => A */

/*@ extern assume :: (boolean) => void */ 

/*@ extern assert :: ({x:boolean|(Prop x)}) => void */ 

/*@ extern requires :: (boolean) => void */ 

/*@ extern ensures :: (boolean) => void */ 

/*@ extern random :: () => number */

/*@ extern pos    :: () => {v:number | v > 0} */


/*************************************************************************/
/*********************** Temporary tag maps ******************************/
/*************************************************************************/
// From:
// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/typeof
//
// Undefined                                                              "undefined"
// Null                                                                   "object"
// Boolean                                                                "boolean"
// Number                                                                 "number"
// String                                                                 "string"
// Host object (provided by the JS environment)  Implementation-dependent
// Function object (implements [[Call]] in ECMA-262 terms)                "function"
// E4X XML object                                                         "xml"
// E4X XMLList object                                                     "xml"
// Any other object                                                       "object"
//
// For Null
// typeof null === 'object'; // This stands since the beginning of JavaScript



/*************************************************************************/
/***************** Types for list Operators ******************************/
/*************************************************************************/

/*@ type list[A]  {  data : A, next : list[A] + null } */

/*@ measure len :: forall A. (list [A]) => number                                                 */

/*@ extern cons  :: forall A. (A, xs:list[A] + null) => {list[A] | (len v) = 1 + (len xs)}               */
/*@ extern nil   :: () => { null | (len v) = 0}                                                           */
/*@ extern head  :: forall A. (xs:list[A]) => A                                                         */
/*@ extern tail  :: forall A. (xs:list [A]) => list [A] + null                                           */
/*@ extern nth   :: forall A. (xs:list [A], {i:number| ((0 <= i) && i < (len xs))}) => A                 */
/*@ extern empty :: forall A. (xango: list[A] + null ) => 
                        {v: boolean | (((Prop v) <=> len(xango) = 0) && ((Prop v) <=> ttag(xango) = "null"))}                      */
/*@ extern emptyPoly :: forall A. (x:A) => {v: boolean | ((Prop v) <=> ((ttag x) = "null"))}             */

/*@ extern length   :: forall A. (xs:list[A] + null) => {v:number | ((v >= 0) && v = (len xs))}         */
/*@ extern safehead :: forall A. (list[A]) => A                                     */
/*@ extern safetail :: forall A. (xs:list[A]) => {v:list[A] + null | (len v) = (len xs) - 1} */

/*@ extern Array    :: (n : { v: number | 0 <= v } ) => { v: [ undefined ] | (len v) = n }               */



/*************************************************************************/
/************************* Type Conversions ******************************/
/*************************************************************************/
/*@ extern sstring  :: forall A. (x: A) => string                               */





/*************************************************************************/
/************** Types for Builtin Operators ******************************/
/*************************************************************************/

/*@ extern builtin_BIBracketRef     :: forall A. (arr:[A], {idx:number | (0 <= idx && idx < (len arr))}) => A           */
/*@ extern builtin_BIBracketAssign  :: forall A. (arr:[A], {idx:number | (0 <= idx && idx < (len arr))}, val:A) => void */
/*@ extern builtin_BIArrayLit       :: forall A. (A) => {v:[A] | (len v) = builtin_BINumArgs}                           */
/*@ extern builtin_BIUndefined     :: forall A. {A | false} */




/*@ extern builtin_OpLT        :: ({x:number|true}, {y:number|true}) => {v:boolean | ((Prop v) <=> (x <  y)) }   */
/*@ extern builtin_OpLEq       :: ({x:number|true}, {y:number|true}) => {v:boolean | ((Prop v) <=> (x <= y)) }   */
/*@ extern builtin_OpGT        :: ({x:number|true}, {y:number|true}) => {v:boolean | ((Prop v) <=> (x >  y)) }   */
/*@ extern builtin_OpGEq       :: ({x:number|true}, {y:number|true}) => {v:boolean | ((Prop v) <=> (x >= y)) }   */

//PV: @==@ and @===@ could be handled more precisely
/*@ extern builtin_OpEq        :: forall A.   (x:A, y:A) => {v:boolean | ((Prop v) <=> (x = y)) }  */
/*@ extern builtin_OpSEq       :: forall A B. (x:A, y:B) => {v:boolean | ((Prop v) <=> (x = y)) }  */
/*@ extern builtin_OpNEq       :: forall A B. (x:A, y:B) => {v:boolean | ((Prop v) <=> (x != y)) } */

/*@ extern builtin_OpLAnd      :: ({x:top|true}, {y:top|true}) => {v:boolean | true}                             */
/*  builtin_OpLAnd      :: ({x:top|true}, {y:top|true}) =>
                            {v:boolean | ((Prop v) <=> (if (falsy x) then (v = y) else (v = x)))}         */

/*@ extern builtin_OpLOr       :: ({x:boolean|true}, {y:boolean|true}) =>
                            {v:boolean | ((Prop v) <=> ((Prop x) || (Prop y)))}                           */

// XXX: Will eventually switch to truthy and falsy:
/*  builtin_OpLOr       :: (x:top, y:top) => 
      { top | ((Prop v) <=> (if (falsy x) then (v = y) else (v = x) ))}           */


//TODO: We would like to have a more precise type (like the following) that 
//would include strings into the game, but this does not work well with 
//equality at the moment:

/*@ extern builtin_OpAdd :: /\ (x:number, y:number) => {number | v = x + y}
                     /\ (x:number, y:string) => string
                     /\ (x:string, y:number) => string
                     /\ (x:string, y:string) => string
  */

/* builtin_OpAdd      :: (x:number + string, y:number + string) => 
                              {v:number + string | (if ((ttag x) = "number" && (ttag y) = "number") 
                                                    then ((ttag v) = "number" && v = x + y) 
                                                    else (ttag v)  = "string")} 
  */

/* builtin_OpAdd       :: ({x:number | true}, {y:number | true})  => {v:number | v = x + y}              */

// The following causes problems with equality. Can't "prove" 0 == (0 + 1) as
// the RHS has type {num | v = 0 + 1} + string. The crucial fact is buried under
// the sum -- the `top-level` refinement is `top` which is useless.

/* builtin_OpAdd       :: (x:number + string, y:number + string) => 
                              {number | ((ttag x) = "number" && (ttag y) = "number" && v = x + y) } + 
                              {string | ((ttag x) = "string" || (ttag y) = "string") } 
                      
  */


/*@ extern builtin_OpSub       :: ({x:number | true}, {y:number | true})  => {v:number | v = x - y}              */
/*@ extern builtin_OpMul       :: (number,  number)  => number                                                   */
/*@ extern builtin_OpDiv       :: (number,  number)  => number                                                   */
/*@ extern builtin_OpMod       :: (number,  number)  => number                                                   */
/*@ extern builtin_PrefixMinus :: ({x:number  | true}) => {v:number  | v = (0 - x)}                              */
/*@ extern builtin_PrefixLNot  :: ({x:boolean | true}) => {v:boolean | ((Prop v) <=> not (Prop x))}              */

//Changing temprorarily until strings are supported
/* extern builtin_PrefixTypeof:: forall A. (A) => string                                                         */


//XXX: Is there an issue with keeping this with a capital P???
/*@ measure Prop        :: (boolean) => bool                              */

/*************************************************************************/
/************** Run-Time Tags ********************************************/
/*************************************************************************/

/*@ measure ttag :: forall A. (A) => string                               */

/*@ extern builtin_PrefixTypeof:: forall A. (x:A) => {v:string | (ttag x) = v }  */

/*@ invariant {v:undefined | ttag(v) = "undefined"} */
/*@ invariant {v:null      | ttag(v) = "null"     } */  //TODO: this is not very precise
/*@ invariant {v:boolean   | ttag(v) = "boolean"  } */ 
/*@ invariant {v:number    | ttag(v) = "number"   } */
/*@ invariant {v:string    | ttag(v) = "string"   } */
/*@ invariant {v:object    | ttag(v) = "object"   } */


/*************************************************************************/
/************** Pre-Loaded Qualifiers ************************************/
/*************************************************************************/

/*@ qualif Bot(v:a)       : 0 = 1                               */
/*@ qualif Bot(v:obj)     : 0 = 1                               */
/*@ qualif Bot(v:bool)    : 0 = 1                               */
/*@ qualif Bot(v:number)     : 0 = 1                            */
/*@ qualif CmpZ(v:number)    : v < 0                            */
/*@ qualif CmpZ(v:number)    : v <= 0                           */
/*@ qualif CmpZ(v:number)    : v >  0                           */
/*@ qualif CmpZ(v:number)    : v >= 0                           */
/*@ qualif CmpZ(v:number)    : v =  0                           */
/*@ qualif CmpZ(v:number)    : v != 0                           */

/*@ qualif Cmp(v:number, x:number)   : v <  x                   */
/*@ qualif Cmp(v:number, x:number)   : v <= x                   */
/*@ qualif Cmp(v:number, x:number)   : v >  x                   */
/*@ qualif Cmp(v:number, x:number)   : v >= x                   */

/*@ qualif Cmp(v:a,x:a)   : v =  x                              */
/*@ qualif Cmp(v:a,x:a)   : v != x                              */
/*@ qualif One(v:number)     : v = 1                            */
/*@ qualif True(v:bool)   : (? v)                               */
/*@ qualif False(v:bool)  : not (? v)                           */
/*@ qualif True1(v:Bool)  : (Prop v)                            */
/*@ qualif False1(v:Bool) : not (Prop v)                        */




// Somewhat more controversial qualifiers (i.e. "expensive"...)

/* qualif Add(v:number,x:number,y:number): v = x + y           */
/* qualif Sub(v:number,x:number,y:number): v = x - y           */


/*@ extern top_level :: () => void */
