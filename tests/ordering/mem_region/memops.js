/*@ include memregion.js */

/*@ memory_region_init :: 
  (number,number,number,number)/emp => <a>/a |-> x:dlist[<a>,null] */
function memory_region_init(offset, size, s_addr, sz) 
{
  var mr = { file_off: offset,
             file_size: size,
             start_addr: s_addr,
             size:sz,
             next:null,
             prev:null };
  return mr;
}

/*@ memory_region_create :: () => {v:<l> | true }/l |-> x:dlist[<l>,null] */
function memory_region_create()
{
  var r = memory_region_init(0,0,0,1);
  var r1 = memory_region_init(0,0,786432,65536);
  r.next = r1;
  r1.prev = r;
  return r;
}

function split_memory_region()
{
}
