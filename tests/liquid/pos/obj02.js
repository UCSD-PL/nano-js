/*@ qualif PLusOne(v:number, w: number)     : v = w + 1                            */

/*@ inc :: (number) => number  */
function inc(n) {
  return n + 1;
}


/*@ foo :: ()/emp => { number | v = 6 }/emp */
function foo () {

  var obj = {
    a: 5,
    b: "String",
    f: inc
  }
  
  var ff = obj.f;
    return 3;
//  return ff(obj.a);

}
