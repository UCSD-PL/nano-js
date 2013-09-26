/*@ map :: ((number) => {v:number | 0 <= v}, <l>)/l |-> list [number] => void/l |-> list [{v:number | 0 <= v}] */
function map(f, xs){
    var d = xs.data;
    var n = xs.next;
    var e = f(d);
    xs.data = e;

    if (typeof(n) != "null") {
        map(f,n);
    }
    else
    {
    }

    return;
}

/*@ abs :: (number) => {v:number | 0 <= v} */
function abs(x){
  if (x <= 0){
    return (0 - x);
  }
  return x;
}

/*@ main :: (<l>)/l |-> list [number] => void/l |-> list [{v:number | 0 <= v}] */
function main(xs){
  var bs = map(abs, xs);
  return;
}
