define relation lseg^(head, tail): 
  ( 
	((head l= tail) & emp) | 
          ((head |-> loc next: nxt; int key: ky) * (lseg^(nxt, tail) & (ky lt-set lseg-keys^(nxt, tail))))  
  ) 
  axiom: ( (sorted^(tail) -* ((lseg-keys^(head, tail) lt keys^(tail)) => (sorted^(head) & (keys^(head) s= (lseg-keys^(head, tail) union keys^(tail)))))) &
	  (((tail |-> loc next: virtual tn; int key: virtual tk) * sorted^(tn)) -* (((lseg-keys^(head, tail) set-lt tk) * true) => ((lseg^(head, tn) & (lseg-keys^(head, tn) s= (lseg-keys^(head, tail) union (singleton tk)))) * sorted^(tn)))) ) ;

define bin-set-fun lseg-keys^(head, tail):
  (case (head l= tail) : emptyset;
   case ((head |-> loc next: nxt; int key: ky) * true): 
   	((singleton ky) union lseg-keys^(nxt, tail));
   default: emptyset
  ) ;



bb insert-nil:
pre: ((sorted^(x) & (kk s= keys^(x))) & (~ (k i-in kk))) ;
post: (sorted^(ret) & (keys^(ret) s= (kk union (singleton k)))) ;
{
	assume (x l== nil);
	malloc y;
	int y.key := k;
	loc ret := y; 
}

bb insert-before-head:
pre: ((sorted^(x) & (kk s= keys^(x))) & (~ (k i-in kk))) ;
post: (sorted^(ret) & (keys^(ret) s= (kk union (singleton k)))) ;
{
	assume (! (x l== nil));
	int xk := x.key;
	assume (k <= xk);
	malloc y;
	int y.key := k;
	loc y.next := x;
	loc ret := y;
}

bb insert-before-loop:
pre: ((sorted^(x) & (kk s= keys^(x))) & (~ (k i-in kk))) ;
post: ( sorted^(x) &
      ( ((sorted^(curr) & ((xk lt-set keys^(curr)) & (~ (k i-in keys^(curr))))) * ((prev |-> loc next: curr; int key: xk) & (xk < k))) * 
       lseg^(x, prev) ) ) ;
{
	assume (! (x l== nil));
	int xk := x.key;
	assume (! (k <= xk));
	loc prev := x;
	loc curr := x.next;
}

bb insert-in-loop:
pre: ( ((sorted^(curr) & ((prevk lt-set keys^(curr)) & (~ (k i-in keys^(curr))))) * ((prev |-> loc next: curr; int key: prevk) & (prevk < k))) * 
       (lseg^(x, prev) & (lseg-keys^(x, prev) set-lt prevk)) ) ;
post: ( ((sorted^(curr1) & ((currk lt-set keys^(curr1)) & (~ (k i-in keys^(curr1))))) * ((prev1 |-> loc next: curr1; int key: currk) & (currk < k))) * 
       (lseg^(x, prev1) & (lseg-keys^(x, prev1) set-lt currk)) ) ;
{
	assume (! (curr l== nil));
	int currk := curr.key;
	assume (! (k <= currk));
	loc prev1 := curr;
	loc curr1 := curr.next;
}

bb insert-after-loop:
pre: ( (((keys^(curr) union (singleton prevk)) union lseg-keys^(x, prev)) s= kk) &
      ( ((sorted^(curr) & ((prevk lt-set keys^(curr)) & (~ (k i-in keys^(curr))))) * ((prev |-> loc next: curr; int key: prevk) & (prevk < k))) * 
       (lseg^(x, prev) & (lseg-keys^(x, prev) set-lt prevk)) ) ) ;
post: (sorted^(x) & (keys^(x) s= (kk union (singleton k)))) ;
{
	int currk := curr.key;
	assume ((curr l== nil) || ((! (curr l== nil)) && (k <= currk)));
	malloc y;
	int y.key := k;
	loc y.next := curr;
	loc prev.next := y;
}


