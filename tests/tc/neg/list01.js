/*@ append :: (x:<l>, number)/l |-> list[number] =>
                          <m>/l |-> list[number] * m |-> list[number] */
function append(x, a) {
  var r = { data:a, next:x };
  return r;
}

