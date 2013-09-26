/*@ foo :: () => <l>/l |-> list [{v:number| 10 < v}] */
function foo() {
  var l = { data: 12, next: null };
  return l;
}

