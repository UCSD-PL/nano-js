/*@ qualif PLusOne(v:number, w: number)     : v = w + 1                            */

/*@ inc :: (number) => number  */
function inc(n) {
  return n + 1;
}

/*@ foo :: ({ number | true } )/emp => <l>/l |-> {  } */
function foo (n) {

  var obj = {
    a: 5,
    b: "String",
    oo: { n: 6 }
  
  }

  
  return obj.oo;

}

