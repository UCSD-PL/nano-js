/*@ sum :: (list [{v:int| 0 <= v}]) => int */
function sum(xs){
  if (isEmpty(xs)) {
    return 0;
  }
  var h = head(xs);
  var t = tail(xs);
  var z = sum(xs);

  return 10; // h + sum(t);
}

