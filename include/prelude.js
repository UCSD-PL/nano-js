/*@ crash :: forall A.() => A */
function crash(){
  return crash();
}


/*@ assume :: (boolean) => void */ 
function assume(p){
  return;
}

/*@ assert :: ({x:boolean|(Prop x)}) => void */ 
function assert(p){
  return;
}

/*@ requires :: (boolean) => void */ 
function requires(p){
  return;
}

/*@ ensures :: (boolean) => void */ 
function ensures(p){
  return;
}

/*@ random :: () => number */
function random(){
  var r = Math.random();
  var x = Math.floor(r * 11);
  return x;
}

/*@ pos    :: () => {v:number | v > 0} */
function pos(){
  var x = random();
  if (x > 0) {
    return x;
  } else {
    return (1 - x);
  }
}

/*@ wind :: (<l>) => <l> */
function wind(x) {
    return x;
}

/*@ unwind :: (<l>) => <l> */
function unwind(x) {
    return x;
}

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

/*@ type list[A]  exists! l |-> list[A]. {  data : A, next : <l> + null } */
/*@ type inflist[A]  exists! l |-> inflist[A]. {  data : A, next : <l> } */

/*@ measure len :: forall A. (list [A]) => number                                                 */

/*@ cons  :: forall A. (A, <m> + null)/m |-> list[A] => <l>/l |-> list [A]                        */
/*@ nil   :: () => null                                                                           */
/*@ head  :: forall A. (xs:<l>)/l |-> list [A] => A/same                                          */
/*@ tail  :: forall A. (xs:<l>)/l |-> list [A] => <m>+null/l |-> { data : A, next :<m>+null} * m |-> list[A] */ 
/*@ nth   :: forall A. (xs:list [A], {i:number| ((0 <= i) && i < (len xs))}) => A                 */
/*@ empty :: forall A. (xango:<l> + null)/l |-> list[A] => 
                        {v: boolean | ((Prop v) <=> (ttag(xango) = "null"))}/same                 */
/*@ emptyPoly :: forall A. (x:A) => {v: boolean | ((Prop v) <=> ((ttag x) = "null"))}             */


/*@ length   :: forall A. (xs:list [A]) => {v:number | ((v >= 0) && v = (len xs))}                */
/*@ safehead :: forall A. ({xs:list [A] | (len xs) > 0}) => A                                     */
/*@ safetail :: forall A. ({xs:list [A] | (len xs) > 0}) => {v:list [A] | (len v) = (len xs) - 1} */



/*************************************************************************/
/************************* Type Conversions ******************************/
/*************************************************************************/
/*@ sstring  :: forall A. (x: A) => string                                                         */





/*************************************************************************/
/************** Types for Builtin Operators ******************************/
/*************************************************************************/

/*@ builtin_OpLT        :: ({x:number|true}, {y:number|true}) => {v:boolean | ((Prop v) <=> (x <  y)) }   */
/*@ builtin_OpLEq       :: ({x:number|true}, {y:number|true}) => {v:boolean | ((Prop v) <=> (x <= y)) }   */
/*@ builtin_OpGT        :: ({x:number|true}, {y:number|true}) => {v:boolean | ((Prop v) <=> (x >  y)) }   */
/*@ builtin_OpGEq       :: ({x:number|true}, {y:number|true}) => {v:boolean | ((Prop v) <=> (x >= y)) }   */

//PV: @==@ and @===@ could be handled more precisely
/*@ builtin_OpEq        :: forall A. ({x:A|true}, {y:A|true}) => {v:boolean | ((Prop v) <=> (x = y)) }    */
/*@ builtin_OpSEq       :: forall A. ({x:A|true}, {y:A|true}) => {v:boolean | ((Prop v) <=> (x = y)) }    */
/*@ builtin_OpNEq       :: forall A B. ({x:A|true}, {y:B|true}) => {v:boolean | ((Prop v) <=> (x != y)) } */

/*@ builtin_OpLAnd      :: ({x:top|true}, {y:top|true}) => {v:boolean | true}                             */
/*  builtin_OpLAnd      :: ({x:top|true}, {y:top|true}) =>
                            {v:boolean | ((Prop v) <=> (if (falsy x) then (v = y) else (v = x)))}         */

/*@ builtin_OpLOr       :: ({x:boolean|true}, {y:boolean|true}) =>
                            {v:boolean | ((Prop v) <=> ((Prop x) || (Prop y)))}                           */

// XXX: Will eventually switch to truthy and falsy:
/*  builtin_OpLOr       :: (x:top, y:top) => 
                             {v:top | ((Prop v) <=> (if (falsy x) then (v = y) else (v = x) ))}           */

/*@ builtin_OpAdd       :: ({x:number | true}, {y:number | true})  => {v:number | v = x + y}              */
/*@ builtin_OpSub       :: ({x:number | true}, {y:number | true})  => {v:number | v = x - y}              */
/*@ builtin_OpMul       :: (number,  number)  => number                                                   */
/*@ builtin_OpDiv       :: (number,  number)  => number                                                   */
/*@ builtin_OpMod       :: (number,  number)  => number                                                   */
/*@ builtin_PrefixMinus :: ({x:number | true}) => {v:number | v = (0 - x)}                                */
/*@ builtin_PrefixLNot  :: (boolean) => boolean                                                           */

//Changing temprorarily until strings are supported
/* builtin_PrefixTypeof:: forall A. (A) => string                                                         */


/*@ measure prop        :: (boolean) => bool                              */

/*************************************************************************/
/************** Run-Time Tags ********************************************/
/*************************************************************************/

/*@ measure ttag :: forall A. (A) => string                               */

/*@ builtin_PrefixTypeof:: forall A. (x:A) => {v:string | (ttag x) = v }  */

/*@ invariant {v:undefined | ttag(v) = "undefined"} */
/*@ invariant {v:null      | ttag(v) = "null"     } */  //TODO: this is not very precise
/*@ invariant {v:boolean   | ttag(v) = "boolean"  } */ 
/*@ invariant {v:number    | ttag(v) = "number"   } */
/*@ invariant {v:string    | ttag(v) = "string"   } */
/*@ invariant {v:object    | ttag(v) = "object"   } */
/*@ invariant {v:<l>       | ttag(v) = "reference"} */


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

/*@ qualif Add(v:number,x:number,y:number): v = x + y           */
/*@ qualif Sub(v:number,x:number,y:number): v = x - y           */


/*@ top_level :: () => void */
