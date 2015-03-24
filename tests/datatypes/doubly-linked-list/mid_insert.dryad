define pred dll^(x):
 (
	 (((x l= nil) & emp) |

	  ((x |-> loc next: y) & (y l= nil))) |

	   (
	        (((x |-> loc next: nxt) * (nxt |-> secondary prev: x)) * true) &
	        (  (x |-> loc next: nxt) * ((~(nxt l= nil)) & dll^(nxt)) )
		)
 );

define pred rev-dll^(x):
 (
	 (((x l= nil) & emp) |

	  ((x |-> loc prev: y) & (y l= nil))) |

	   (
	        (((x |-> loc prev: prv) * (prv |-> secondary next: x)) * true) &
	        (  (x |-> loc prev: prev) * ((~(prev l= nil)) & rev-dll^(prv)) )
		)
 );
	 
define set-fun keys^(x):
  (case (x l= nil): emptyset;
   case ((x |-> loc next: nxt; int key: ky) * true): 
   	((singleton ky) union keys^(nxt));
   default: emptyset
  ) ;

define set-fun rev-keys^(x):
  (case (x l= nil): emptyset;
   case ((x |-> loc prev: prv; int key: ky) * true): 
   	((singleton ky) union rev-keys^(prv));
   default: emptyset
  ) ;


bb insert-at-middle-both-nil:
pre: (((dll^(v) & (keys^(v) s= vks)) * (rev-dll^(u) & (rev-keys^(u) s= uks))) &
	(((u l= nil) | ((u |-> loc next: v) * true)) &
       ((v l= nil) | ((v |-> loc prev: u) * true)))
     ) ;
post: (((dll^(ret) & (keys^(ret) s= (vks union (singleton k)))) * (rev-dll^(u) & (rev-keys^(u) s= uks))) &
	(((u l= nil) | ((u |-> loc next: ret) * true)) &
       ((ret |-> loc prev: u) * true))
     ) ;
{
	assume (u l== nil);
	assume (v l== nil);
	malloc ret;
	loc ret.prev := u;
	loc ret.next := v;
	int ret.key := k;
}

bb insert-at-middle-u-nil:
pre: (((dll^(v) & (keys^(v) s= vks)) * (rev-dll^(u) & (rev-keys^(u) s= uks))) &
	(((u l= nil) | ((u |-> loc next: v) * true)) &
       ((v l= nil) | ((v |-> loc prev: u) * true)))
     ) ;
post: (((dll^(ret) & (keys^(ret) s= (vks union (singleton k)))) * (rev-dll^(u) & (rev-keys^(u) s= uks))) &
	(((u l= nil) | ((u |-> loc next: ret) * true)) &
       ((ret |-> loc prev: u) * true))
     ) ;
{
	assume (u l== nil);
	assume (! (v l== nil));
	malloc ret;
	loc ret.prev := u;
	loc ret.next := v;
	int ret.key := k;
	loc v.prev := ret;
}

bb insert-at-middle-v-nil:
pre: (((dll^(v) & (keys^(v) s= vks)) * (rev-dll^(u) & (rev-keys^(u) s= uks))) &
	(((u l= nil) | ((u |-> loc next: v) * true)) &
       ((v l= nil) | ((v |-> loc prev: u) * true)))
     ) ;
post: (((dll^(ret) & (keys^(ret) s= (vks union (singleton k)))) * (rev-dll^(u) & (rev-keys^(u) s= uks))) &
	(((u l= nil) | ((u |-> loc next: ret) * true)) &
       ((ret |-> loc prev: u) * true))
     ) ;
{
	assume (! (u l== nil));
	assume (v l== nil);
	malloc ret;
	loc ret.prev := u;
	loc ret.next := v;
	int ret.key := k;
	loc u.next := ret;
}

bb insert-at-middle-no-nil:
pre: (((dll^(v) & (keys^(v) s= vks)) * (rev-dll^(u) & (rev-keys^(u) s= uks))) &
	(((u l= nil) | ((u |-> loc next: v) * true)) &
       ((v l= nil) | ((v |-> loc prev: u) * true)))
     ) ;
post: (((dll^(ret) & (keys^(ret) s= (vks union (singleton k)))) * (rev-dll^(u) & (rev-keys^(u) s= uks))) &
	(((u l= nil) | ((u |-> loc next: ret) * true)) &
       ((ret |-> loc prev: u) * true))
     ) ;
{
	assume (! (u l== nil));
	assume (! (v l== nil));
	malloc ret;
	loc ret.prev := u;
	loc ret.next := v;
	int ret.key := k;
	loc u.next := ret;
	loc v.prev := ret;
}


