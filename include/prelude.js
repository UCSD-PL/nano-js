/*@ crash :: forall A.() => A */
function crash(){
  return crash();
}


/*@ assume :: (p:boolean)/emp => {v:void | (Prop p)}/emp */ 
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

/* wind :: (<l>) => <l> */
function wind(x) {
    return x;
}

/* unwind :: (<l>) => <l> */
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
/* measure min :: forall A. (sList[A]) => A */
/*@ cmp :: forall A. (x:A, y:A) => {v:boolean | (Prop(v) <=> (x <= y))} */
/*@ cmpLT :: forall A. (x:A, y:A) => {v:boolean | (Prop(v) <=> (x < y))} */

/* type inflist[A]  exists! l |-> xs:inflist[A]. r:{  data : A, next : <l> }*/

/* cons  :: forall A. (A, <m> + null)/m |-> list[A] => <l>/l |-> list [A]                        */
/* head  :: forall A. (xs:<l>)/l |-> list [A] => A/same                                          */
/* tail  :: forall A. (xs:<l>)/l |-> list [A] => <m>+null/l |-> { data : A, next :<m>+null} * m |-> list[A] */ 
/* nth   :: forall A. (xs:list [A], {i:number| ((0 <= i) && i < (len xs))}) => A                 */
/* empty :: forall A. (xango:<l> + null)/l |-> list[A] => 
                        {v: boolean | ((Prop v) <=> (ttag(xango) = "null"))}/same                 */
/* emptyPoly :: forall A. (x:A) => {v: boolean | ((Prop v) <=> ((ttag x) = "null"))}             */


/* length   :: forall A. (xs:list [A]) => {v:number | ((v >= 0) && v = (len xs))}                */
/* safehead :: forall A. ({xs:list [A] | (len xs) > 0}) => A                                     */
/* safetail :: forall A. ({xs:list [A] | (len xs) > 0}) => {v:list [A] | (len v) = (len xs) - 1} */




/*************************************************************************/
/************************* Type Conversions ******************************/
/*************************************************************************/
/*@ sstring  :: forall A. (x: A) => string                                                         */





/*************************************************************************/
/************** Types for Builtin Operators ******************************/
/*************************************************************************/

/*@ builtin_OpLT        :: forall A. ({x:A|true}, {y:A|true}) => {v:boolean | ((Prop v) <=> (x <  y)) }   */
/*@ builtin_OpLEq       :: forall A. ({x:A|true}, {y:A|true}) => {v:boolean | ((Prop v) <=> (x <= y)) }   */
/*@ builtin_OpGT        :: ({x:number|true}, {y:number|true}) => {v:boolean | ((Prop v) <=> (x >  y)) }   */
/*@ builtin_OpGEq       :: ({x:number|true}, {y:number|true}) => {v:boolean | ((Prop v) <=> (x >= y)) }   */

//PV: @==@ and @===@ could be handled more precisely
/*@ builtin_OpEq        :: forall A. (x:{v:A|true}, y:{v:A|true}) => {e:boolean | ((Prop e) <=> (x = y)) }    */
/*@ builtin_OpSEq       :: forall A. (v:{x:A|true}, v:{y:A|true}) => {v:boolean | ((Prop v) <=> (x = y)) }    */
/*@ builtin_OpNEq       :: forall A B. (x:{v:A|true}, y:{v:B|true}) => {e:boolean | ((Prop e) <=> (x != y)) } */

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
/*@ builtin_OpMul       :: (x:number,  y:number)  => {v:number | v = (x*y)}                               */ 
/*@ builtin_OpDiv       :: (number,  number)  => number                                                   */
/*@ builtin_OpMod       :: (number,  number)  => number                                                   */
/*@ builtin_PrefixMinus :: ({x:number | true}) => {v:number | v = (0 - x)}                                */
/*@ builtin_PrefixLNot  :: (boolean) => boolean                                                           */

//Changing temprorarily until strings are supported
/* builtin_PrefixTypeof:: forall A. (A) => string                                                         */
/*@ builtin_PrefixDelete:: forall A. (<l>)/l |-> A => void/emp                                             */


/*@ measure prop        :: (boolean) => bool                              */
/* measure field_Ref   :: forall A. (A, string) => <l>                */
/* measure field_int   :: forall A. (A, string) => number             */
/* measure field_A     :: forall A. (A, string) => number             */

/*************************************************************************/
/************** Run-Time Tags ********************************************/
/*************************************************************************/

/*@ measure ttag :: forall A. (A) => string                               */

/*@ builtin_PrefixTypeof:: forall A. (x:A) => {v:string | (ttag x) = v }  */

/*@ measure null :: null */
/*@ measure nil :: forall A. (A) => number */

/* invariant {v:undefined | ttag(v) = "undefined"} */
/*@ invariant {e:null      | (Prop(nil(e)) && e = null) } */  //TODO: this is not very precise
/* invariant {v:boolean   | ttag(v) = "boolean"  } */ 
/* invariant {v:number    | ttag(v) = "number"   } */
/* invariant {v:string    | ttag(v) = "string"   } */
/*@ invariant {v:object    | ttag(v) = "object"   } */
/*@ invariant {e:<l>       | ((~Prop(nil(e))) && (e != null))  } */ 
/*@ invariant {e:<l>+null       | ((Prop(nil(e)) <=> (e = null)))  } */ 
/* invariant {v:<u>       | ttag(v) = "ref(u)"} */
/* invariant {v:<v>       | ttag(v) = "ref(v)"} */
/* invariant {v:<r>       | ttag(v) = "ref(r)"} */


/*************************************************************************/
/************** Pre-Loaded Qualifiers ************************************/
/*************************************************************************/

/*@ qualif Null(v:T,x:T): (Prop(nil(v)) <=> Prop(nil(x))) */
/*@ qualif RApp(v:a): papp1(r, v)                                             */
/*@ qualif PApp(v:a): (papp1 p v) */
/*@ qualif Bot(v:a)       : 0 = 1                               */
/*@ qualif Bot(v:obj)     : 0 = 1                               */
/*@ qualif Bot(v:bool)    : 0 = 1                               */
/*@ qualif Bot(v:number)  : 0 = 1                               */
/*@ qualif Bot(v:Ref)     : 0 = 1                               */
/*@ qualif Bot(v:Rec)     : 0 = 1                               */
/*@ qualif Bot(v:T)     : 0 = 1                               */
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
/*@ qualif One(v:a)       : v = 1                            */
/*@ qualif True(v:bool)   : (? v)                               */
/*@ qualif False(v:bool)  : not (? v)                           */
/*@ qualif True1(v:Bool)  : (Prop v)                            */
/*@ qualif False1(v:Bool) : not (Prop v)                        */



// Somewhat more controversial qualifiers (i.e. "expensive"...)

/* qualif Add(v:number,x:number,y:number): v = x + y           */
/* qualif Sub(v:number,x:number,y:number): v = x - y           */


/*@ top_level :: () => void */

/*
  type mlist[A] exists! l |-> xs:{mlist[A]} . { data:A, next:<l>+null }

    with keys(v) = Set_cup ((Set_sng A)
                            (if (ttag next) = "null" then
                               Set_emp
                             else
                               keys(xs))

         length(v) = 1 + (if (ttag next) = "null" then
                            0
                          else
                            length(xs))
*/

/*

G |- H = H0 * H * l |-> x:T
G |- C[A] = ∃! H' . T'
T = { ... fⱼ:Tⱼ ... } 
T' = { ... fⱼ':Tⱼ' ... }
//... subtyping ...
G |- Tf = {v:C[T] | ∧ θM_c }
θ = [x/v;fⱼ/fⱼ'...]
z fresh
H' = H0 * l |-> {v | v = z}
G' = G;z:Tf
-------------------
G,H |- fold l : G'/H'

*/

