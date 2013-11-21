/*@ qualif G10(v:number)   : v > 10    */

/*@ hop :: (<l>+null)/l |-> list [{v:number| 10 < v}] => <m>/m |-> list [{v:number| 5 < v}] */
function hop(xs){
  if (typeof(xs) == "null") {
    // return { data: 15, next: null };
    x = { data: 15, next: null };
    return x;
  }
  else {
    return xs;
  }
}

