/*@ qualif Plus(v:number, x:number, y:number)   : v = x + y    */

/*@ sumLoop :: ({acc:number | true}, {i:number| 0 <= i}) => {v:number|v = acc + i} */
function sumLoop(acc, i){
  var r = 0;
  if (0 < i){
    r = sumLoop(acc + 1, i - 1);
  } else {
    r = acc;
  }
  return r;
}

/*@ main :: () => void */
function main(){
  var n = pos();
  var m = sumLoop(0, n);
  assert(m == n);
}
