/*@ abs :: ({ x:number | true }) => number */ 
function abs(x){
  var y = x;
  if (x) {
    y = x;
  } else {
    y = 10 + x;
  }
  assert(y > 10);
  assert(y >= 100);
  return y;
}
