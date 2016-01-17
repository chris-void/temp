
#include "share/atspre_staload.hats"

(*
** AVL tree in proof form
*)
datasort
AVLtree =
| leaf of ()
| node of (AVLtree, AVLtree)
// end of [AVLtree]

dataprop
AVLequal (AVLtree, AVLtree) =
| AVLequal_l (leaf, leaf) of ()
| {t1l,t1r:AVLtree}{t2l,t2r:AVLtree}
  AVLequal_n (node (t1l, t1r), node (t2l, t2r)) of
    (AVLequal (t1l, t2l), AVLequal(t1r, t2r))
// end of [AVLequal]

(* AVL tree height *)
dataprop
AVLheight (AVLtree, int) =
| AVLheight_l (leaf (), 0) of ()
| {t1,t2:AVLtree}{h1,h2:nat}
  AVLheight_n (node (t1, t2), 1+ max(h1, h2)) of
    (AVLheight(t1, h1), AVLheight(t2, h2))
// end of [AVLheight]

(* AVL tree size *)
dataprop
AVLsize (AVLtree, int) =
| AVLsize_l (leaf (), 0) of ()
| {t1,t2:AVLtree}{s1,s2:nat}
  AVLsize_n (node (t1, t2), s1+s2+1) of (AVLsize(t1, s1), AVLsize(t2, s2))
// end of [AVLsize]

(* AVL tree shortest path *)
dataprop
AVLshortestpath (AVLtree, int) =
| AVLshortestpath_l (leaf (), 0) of ()
| {t1,t2:AVLtree}{sp1,sp2:nat}
  AVLshortestpath_n (node (t1, t2), 1+ min (sp1, sp2)) of
    (AVLshortestpath(t1, sp1), AVLshortestpath(t2, sp2))
// end of [shortestpath]

dataprop isAVL (AVLtree) =
| {t1,t2:AVLtree} {n1,n2:nat | n1 <= n2+1; n2 <= n1+1}
  isAVL_n (node (t1, t2)) of (isAVL t1, isAVL t2, AVLheight (t1, n1), AVLheight (t2, n2))
| isAVL_l (leaf ()) of ()
// end of [isAVL]

exception ElementAlreadyExists of ()
exception ElementDoesntExist   of ()

(* ***** ***** *)
(*
// prove that AVLequal is functional
-> seems not necessary

prfun
AVLequal_isfun{t1,t2:AVLtree}
(pf1: AVLtree, pf2: AVLtree) =
*)

(* prove that AVLsize is a total relation on the two arguments *)
prfun
AVLsize_istot {t:AVLtree} .<t>. (
  ): [s:nat] AVLsize (t, s) =
scase t of
| leaf () => AVLsize_l ()
| node (tl, tr) = AVLsize_n (AVLsize_istot{tl} (), AVLsize_istot{tr} ())
// end of [AVLsize_istot]

(* prove that AVLsize is functional on the two arguments *)
prfun
AVLsize_isfun{t:AVLtree}{s1,s2:nat} .<t>.
(
  pf1: AVLsize (t, s1), pf2: AVLsize(t, s2)
): [s1==s2] void =
case+ (pf1, pf2) of
| (AVLsize_l (), AVLsize_l ()) => ()
| (AVLsize_n (pf11, pf12), AVLsize_n (pf21, pf22)) =>
  let
    prval () = AVLsize_isfun (pf11, pf21)
    prval () = AVLsize_isfun (pf12, pf22)
  in
    //empty
  end
// end of [AVLsize_isfun]


(*  prove that AVLheight is a total relation on two arguments  *)
prfun
AVLheight_istot {t:AVLtree} .<t>. (
  ): [h:nat] AVLheight (t, h) =
scase t of
| leaf () => AVLheight_l ()
| node (tl, tr) => AVLheight_n (AVLheight_istot{tl} (), AVLheight_istot {tr} ())
// end of [AVLheight_istot]

(*  prove that AVLheight is functional on the two arguments  *)
prfun
AVLheight_isfun{t:AVLtree}{h1,h2:nat} .<t>.
(
  pf1: AVLheight (t, h1), pf2: AVLheight (t, h2)
): [h1==h2] void =
case+ (pf1, pf2) of
| (AVLheight_l (), AVLheight_l ()) => ()
| (AVLheight_n (pf11, pf12), AVLheight_n (pf21, pf22)) =>
  let
    prval () = AVLheight_isfun (pf11, pf21)
    prval () = AVLheight_isfun (pf12, pf22)
  in
    //empty
  end
// end of [AVLheight_isfun]


(*  prove that AVLshortestpath is a total relation on two arguments  *)
prfun
AVLshortestpath_istot {t:AVLtree} .<t>. (
  ): [sp:nat] AVLshortestpath (t, sp) =
scase t of
| leaf () => AVLshortestpath_l ()
| node (tl,tr) =>
    AVLshortestpath_n (AVLshortestpath_istot{tl}(), AVLshortestpath_istot{tr}())
// end of [AVLshortestpath_istot]

(*  prove that AVLshortestpath is functional on the two arguments  *)
prfun
AVLshortestpath_isfun{t:AVLtree}{sp1,sp2:nat} .<t>.
(
  pf1: AVLshortestpath (t,sp1), pf2: AVLshortestpath (t, sp2)
): [sp1==sp2] void =
case+ (pf1, pf2) of
| (AVLshortestpath_l (), AVLshortestpath_l ()) => ()
| (AVLshortestpath_n (pf11, pf12), AVLshortestpath_n (pf21, pf22)) =>
  let
    prval () = AVLshortestpath_isfun (pf11, pf21)
    prval () = AVLshortestpath_isfun (pf12, pf22)
  in
    //empty
  end
// end of [AVLshortestpath_isfun]

//prfun isAVL_isfun
//prfun isAVL_istot

(* ***** ***** *)

(*
** AVL tree using independent type
*)
datatype
avltree (key:t@ype, value:t@ype, int(*height*)) =
| AVL_leaf (key, value, 0) of ()
| {hl,hr:nat | ~1 <= hl-hr; hl-hr <= 1}
  AVL_node (key, value, 1+ max (hl, hr)) of
    (key, value, avltree (key, value, hl), avltree(key, value, hr))
// end of [avltree]
typedef avltree (key:t@ype, value:t@ype) = [n:nat] avltree(key, value, n)

//assume avltree (key, value) = avltree (key, value)

(* AVL tree height *)
fun
{key:t@ype}{value:t@ype}
height
{h:nat}(
  tree: avltree (key, value, h)
): int h =
case+ tree of
| AVL_leaf () => 0
| AVL_node (_, _, tl, tr) => 1+ max (height (tl), height (tr))
// end of [height]

(* AVL tree shortest path *)
fun
{key:t@ype}{value:t@ype}
shortestpath
{h:nat}(
  tree: avltree (key, value, h)
): int =
case+ tree of
| AVL_leaf () => 0
| AVL_node (_, _, tl ,tr) => 1+ min (shortestpath(tl), shortestpath(tr))
// end of [height]

(* AVL tree size *)
fun
{key:t@ype}{value:t@ype}
size
{h:nat}(
  tree: avltree (key, value, h)
): int =
case+ tree of
| AVL_leaf () => 0
| AVL_node (_, _, tl, tr) => 1+ size(tl) + size(tr)
// end of [size]

fun
{key:t@ype}{value:t@ype}
isMember
{h:nat}(
  tree: avltree (key, value, h), k: key, cmp: (key, key) -> int
): bool =
case+ tree of
| AVL_leaf () => false
| AVL_node  (current, _, tl, tr) =>
    if cmp (current, k) = 0 then true
    else if cmp (current, k) > 0
      then isMember (tl, k, cmp)
      else isMember (tr, k, cmp)
// end of [isMember]

fun
{key:t@ype}{value:t@ype}
isEmpty
{h:nat}(
  tree: avltree (key, value, h)
): bool =
case+ tree of
| AVL_leaf () => true
| _ => false
// end of [isEmpty]

fun
{key:t@ype}{value:t@ype}
isPerfect
{h:nat}(
  tree: avltree(key, value, h)
): bool =
case+ tree of
| AVL_leaf () => true
| AVL_node (_, _, tl, tr) =>
    isPerfect(tl) && isPerfect(tr) && height(tl) = height(tr)
// end of [isPerfect]

(* ***** ***** *)

fun
{key:t@ype}{value:t@ype}
rotate_left
{hl,hr:nat | hr-hl==2}(
  k:key, v:value, tl: avltree(key, value, hl), tr:avltree(key, value, hr)
): [h:nat | hr <= h; h <= hr+1] avltree(key, value, h) = let
  val AVL_node (rkey, rvalue, rl, rr) = tr
in
  if height(rl) <= height(rr)
  then AVL_node (rkey, rvalue, AVL_node(k, v, tl, rl), rr)
  else let
    val AVL_node (rlk, rlv, rll, rlr) = rl
  in
    AVL_node (rlk, rlv, AVL_node(k,v, tl, rll), AVL_node (rkey, rvalue, rlr, rr))
  end
end
// end of [rotate_left]

fun
{key:t@ype}{value:t@ype}
rotate_right
{hl,hr:nat | hl-hr==2}(
  k:key, v:value, tl:avltree(key, value, hl), tr:avltree(key, value, hr)
): [h:nat | hl <= h; h <= hl+1] avltree(key, value, h) = let
  val AVL_node (lk, lv, ll, lr)= tl
in
  if height (ll) >= height (lr)
  then AVL_node (lk, lv, ll, AVL_node (k, v, lr, tr))
  else let
    val AVL_node (lrk, lrv, lrl, lrr) = lr
  in
    AVL_node (lrk, lrv, AVL_node (lk, lv, ll, lrl), AVL_node (k, v, lrr, tr))
  end
end
// end of [rotate_right]

(* ***** ***** *)

fun
{key:t@ype}{value:t@ype}
avltree_insert
(
  tree: avltree (key, value), k: key, v: value, cmp: (key, key) -> int
): avltree (key, value) = let
fun insert {h:nat} (t: avltree (key, value, h)): [hh:nat|h <= hh; hh <= h+1] avltree (key, value, hh) =
		case+ t of
		| AVL_leaf () => AVL_node (k, v, AVL_leaf (), AVL_leaf ())
		| AVL_node (current_key, current_value, left, right) =>
			if cmp (k, current_key) < 0 then
				let
					val t = insert left
				in
					if height t - height right > 1
					then rotate_right (current_key, current_value, t, right)
					else AVL_node (current_key, current_value, t, right)
				end
			else if cmp (k, current_key) > 0 then
				let
					val t = insert right
				in
					if height t - height left > 1
					then rotate_left (current_key, current_value, left, t)
					else AVL_node (current_key, current_value, left, t)
				end
			else
				$raise ElementAlreadyExists ()
in
	insert tree
end


fun
{key:t@ype} {value:t@ype}
avltree_replace
(
  tree: avltree (key, value), k: key, v: value, cmp: (key, key) -> int
): avltree (key, value) =
case+ tree of
| AVL_leaf () => $raise ElementDoesntExist ()
| AVL_node (current, _, left, right) =>
  if cmp (k, current) > 0
  then avltree_replace (right, k, v, cmp)
	else if cmp (k, current) < 0
    then avltree_replace (left, k, v, cmp)
    else AVL_node (current, v, left, right)

fun
{key:t@ype} {value:t@ype}
avltree_delete
(
  tree: avltree (key, value), k:key, cmp: (key, key) -> int
): avltree (key, value) = let
  fun find_min (tree: avltree (key, value)): (key, value) =
	case+ tree of
	| AVL_node (k, v, AVL_leaf (), _) => (k, v)
	| AVL_node (_, _, left, _)      => find_min left
	| AVL_leaf ()                   => $raise ElementDoesntExist () (* this should not happen *)

  fun delete {h:nat} (tree: avltree (key, value, h), k: key): [hh:nat|h-1 <= hh; hh <= h] avltree (key, value, hh) =
  case+ tree of
  | AVL_leaf () => $raise ElementDoesntExist ()
  | AVL_node (current, _, AVL_leaf (), AVL_leaf ()) =>
  		if cmp (current, k) = 0
  		then AVL_leaf ()
  		else $raise ElementDoesntExist ()
  | AVL_node (current, v, left, right) =>
  		if cmp (k, current) < 0
      then let
  			val newleft = delete (left, k)
  		in
  			if height right - height newleft > 1
  			then rotate_left (current, v, newleft, right)
  			else AVL_node (current, v, newleft, right)
  		end
  		else if cmp (k, current) > 0
      then let
  			val newright = delete (right, k)
  		in
  			if height left - height newright > 1
  			then rotate_right (current, v, left, newright)
  			else AVL_node (current, v, left, newright)
  		end else
  		case+ (left, right) of
  		| (AVL_leaf (), _) => right
  		| (_, AVL_leaf ()) => left
  		| (_, _) => let
          val (mink, minv) = find_min right
  			  val newright = delete (right, mink)
  			in
  				if height left - height newright > 1
  				then rotate_right (mink, minv, left, newright)
  				else AVL_node (mink, minv, left, newright)
  			end
  in
  	delete (tree, k)
  end

fun
{key:t@ype} {value:t@ype}
avltree_insert_or_replace
(
  tree: avltree (key, value), k:key, v:value, cmp: (key, key) -> int
): avltree (key, value) =
if isMember (tree, k, cmp)
then avltree_replace (tree, k, v, cmp)
else avltree_insert (tree, k, v, cmp)
