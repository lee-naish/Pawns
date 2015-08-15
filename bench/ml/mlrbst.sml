(* SML bst with refs and := *)

datatype tree = mt | node of (tree ref) * int * (tree ref);

fun ints_from_to(min, max) =
	if min <= max then
		min :: ints_from_to (min+1, max)
	else 
		[];

fun bst_size(t) =
    case t of
	  mt => 0
    	| (node (l, n, r)) => 1 + bst_size(!l) + bst_size(!r);

fun bst_insert_du(x, t0) =
    case t0 of
    	  ref mt => t0 := node(ref mt, x, ref mt)
    	| ref (node(l, n, r)) =>
        	if x<=n then
            		bst_insert_du(x, l)
        	else
		    	bst_insert_du(x, r);

fun list_bst_du(xs, t0) =
    case xs of
    	  [] => ()
    	| (x:: xs1) =>
	    let  in
		bst_insert_du(x, t0);
		list_bst_du(xs1, t0)
	    end;

fun list_bst(xs) =
	let val tp = ref mt in
	    list_bst_du(xs, tp);
	    !tp
	end;

fun test n = bst_size(list_bst(ints_from_to(1,n)));

print (Int.fmt StringCvt.DEC (test 30000));
print "\n";
