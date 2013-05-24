// HINT: Recall the `invariant` for the corresponding test in tests/esc/pos
//       Find a way to represent that invariant as a qualifier (or a conjunction of qualifiers.)
//       You can use operators like <=>, =>, &&, || in the qualifiers.

/*@ create :: () => int */
function create(){
  return 0;
}

/*@ acquire :: (int) => int */
function acquire(l){
  assert(l == 0);
  return 1;
}

/*@ release :: (int) => int */
function release(l){
  assert(l != 0);
  return 0;
}

/*@ driver :: (int, int, int) => int */ 
function driver(l, newCount, oldCount){
  if (newCount != oldCount){
    l        = acquire(l);
    oldCount = newCount;
    if (0 < newCount){
      l = release(l);
      newCount = newCount - 1;
    } else {
      newCount = newCount;
    }
    l = driver(l, newCount, oldCount);
  }
  return l;
}

/*@ main :: () => void */
function main() {
  var newCount = pos();
  var oldCount = pos(); 
  var l        = create();
  if (newCount < oldCount) {
    l = driver(l, newCount, oldCount); 
    l = release(l);
  }
}

