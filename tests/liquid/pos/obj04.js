
/*@ foo :: () => { v: number | v = 1 } */
function foo () {
  var obj = {f1: {f11: 1} };
  return obj["f1"].f11 + obj.f1["f11"] + obj["f1"]["f11"];
}
