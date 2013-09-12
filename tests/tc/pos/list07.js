
/*@ type nlist  list[number] */ 

/*@ foo :: () => <l>/l |-> nlist */
function foo() {
  l = { data: 5, more_data: 6, next: null  } ;
//  wind(l, nlist);
  return l;
}
