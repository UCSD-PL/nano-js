
/*@ type nlist  list[number] */ 

/*@ foo :: (x:<l> + number)/l |-> nlist + number) => nlist */
function foo(x) {
  return { data: 5, next: x   } ;
}
