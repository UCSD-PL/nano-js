/*@ include singly-linked-list.js */

/*@ 
ltest ::
 (x:{v:<l>+null | (Prop(nil(v)) => Prop(nil(xs)))})/l |-> xs:list[number] => <l>+null/l |-> xs1:{v:list[number] | len(v) >= 0}
*/
function ltest(x) {
  if (x != null) {
    var k = x.data
    return x;
  }
  
  return x;
}
