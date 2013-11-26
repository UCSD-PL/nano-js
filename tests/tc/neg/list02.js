/*@ main :: (x:<l>, a:number + boolean)/l |-> list[number] => <m>/l |-> list[number] * m |-> list[number] */
function main(x, a) {
  var r = { data:a, next:x };
  return r;
}


