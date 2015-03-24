// ---- Commmon definitions for singly-linked list examples  ----
#include <vcc.h>
#include <stdlib.h>

typedef 
/*D_tag node */
struct node {
  int key;
  struct node * next;
} SNnode;

/*D_defs
define pred sll^(x): 
  ( 
  ((x l= nil) & emp) | 
  ((x |-> loc next: nxt) * sll^(nxt))  
  ) ;
  
define set-fun keys^(x):
  (case (x l= nil): emptyset;
   case ((x |-> loc next: nxt; int key: ky) * true): 
    ((singleton ky) union keys^(nxt));
   default: emptyset
  ) ;*/
// --------------------------------------------------------------

_(dryad)
SNnode * sll_delete_all(SNnode * x, int k)
  /*D_requires sll^(x) */
  /*D_ensures (sll^(ret) & (((k i-in old(keys^(x))) => (keys^(ret) s= (old(keys^(x)) setminus (singleton k)))) &
                 ((~ (k i-in old(keys^(x)))) => (keys^(ret) s= old(keys^(x)))))) */
{
	if (x == NULL) {
		return x;
	} else if (x->key == k) {
		SNnode * tmp = sll_delete_all(x->next, k);
		free(x);
		return tmp;
	} else {
		SNnode * tmp = sll_delete_all(x->next, k);
		x->next = tmp;
		return x;
	}
}

