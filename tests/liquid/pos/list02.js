/*@ listsum :: (list [{v:int | 0 <= v}]) => {v:int | 0 <= v} */
function listsum(xs){
  if (isEmpty(xs)) {
    return 0;
  }
  var h = head(xs);
  var t = tail(xs);
  return h + listsum(t);
}

