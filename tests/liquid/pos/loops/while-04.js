/*@ qualif Ineq1(v : number ): (v <= 5) */
/*@ qualif Eq1(v:number, i:number): v = i - 1 */

/*@ foo :: () => { number | v = 4 } */ 
function foo() {
  var x = 0;
  var i = 1; 
  assert(x == i - 1); // NOT OK, WTF?
  while (i < 5) {
     x = i;
     i = i + 1; 
     // assert(x == i - 1);
  }
  assert(i == 5);     // OK
  assert(x < i);      // NOT OK, WTF?
  assert(x == i - 1); // NOT OK, WTF?
  return x;
}
