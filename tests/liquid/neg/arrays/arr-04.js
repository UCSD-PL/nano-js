
/*@ writeIndex :: (a:[number], i:{ number | ( v < (len a)) }) => void */
function writeIndex(a, i) {
  a[i] = 10;
  return;
}
