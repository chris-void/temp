
#include "share/atspre_staload.hats"

(*
** AVL tree in proof form
*)
datasort
AVLtree =
| leaf of ()
| node of (AVLtree, AVLtree)

dataprop
AVLequal (AVLtree, AVLtree) =
| AVLequal_l (leaf, leaf) of ()
| {t1l,t1r:AVLtree}{t2l,t2r:AVLtree}
  AVLequal_n (node (t1l, t1r), node (t2l, t2r)) of (AVLequal (t1l, t2l), AVLequal(t1r, t2r))

//prfun 
//isEqual

(* AVL tree height *)
dataprop
AVLheight (AVLtree, int) =
| AVLheight_l (leaf (), 0) of ()
| {t1,t2:AVLtree}{h1,h2:nat}
  AVLheight_n (node (t1, t2), 1+ max(h1, h2)) of
    (AVLheight(t1, h1), AVLheight(t2, h2))

dataprop isAVL (AVLtree) =
| {t1,t2:AVLtree} {n1,n2:nat | n1 <= n2+1; n2 <= n1+1}
  isAVL_B (node (t1, t2)) of (isAVL t1, isAVL t2, AVLheight (t1, n1), AVLheight (t2, n2))
| isAVL_E (leaf ())
// end of [isAVL]

//prfun lemma_existence

//prfun lemma_un

(* AVL tree size *)
dataprop
AVLsize (AVLtree, int) =
| AVLsize_l (leaf (), 0) of ()
| {t1,t2:AVLtree}{s1,s2:nat}
  AVLsize_n (node (t1, t2), s1+s2+1) of (AVLsize(t1, s1), AVLsize(t2, s2))

(* AVL tree shortest path *)
dataprop
AVLshortestpath (AVLtree, int) =
| AVLshortestpath_l (leaf (), 0) of ()
| {t1,t2:AVLtree}{sp1,sp2:nat}
  AVLshortestpath_n (node (t1, t2), 1+ min (sp1, sp2)) of
    (AVLshortestpath(t1, sp1), AVLshortestpath(t2, sp2))


//typedef cpm_t (a:t@ype) = (a, a) -<fun> Sgn

exception ElementAlreadyExists of ()
exception ElementDoesntExist   of ()

(* ***** ***** *)

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
(*
prfun AVLshortestpath_istot {t:AVLtree} .<t>. (): [sp:nat] AVLshortestpath (t, sp) = 
  sif t > 0
  then  AVLshortestpath_n (AVLshortestpath_istot{t-1}, AVLshortestpath_istot{t-1})
  else AVLshortestpath_l () 
*)
//prfun trsz_istot {t:tree} (): [n:nat] trsz (t, n) 
(*
prfun AVLshortestpath_istot{t:AVLtree}{sp:nat} .<t>.
() :[sp:nat] AVLshortestpath (t, sp) =
  sif isEqual (t, leaf) 
  then let 
    prval (t1, t2) = node (t)
  in 
    AVLshortestpath_n (AVLshortestpath_istot{t1}{sp} (), AVLshortestpath_istot{t2}{sp} ())
  end 
  else AVLshortestpath_l ()
*)
  dataprop
  EXP2 (int, int) =
    | EXP2bas (0, 1)
    | {n:nat}{p:nat}
      EXP2ind (n+1, 2*p) of EXP2 (n, p)
  // end of [EXP2]
  prfun exp2_istot {n:nat} .<n>. (): [p:nat] EXP2 (n, p) =
    sif n > 0 then EXP2ind (exp2_istot {n-1} ()) else EXP2bas ()

  prfun exp2_isfun {n:nat} {p1,p2:int} .<n>.
    (pf1: EXP2 (n, p1), pf2: EXP2 (n, p2)): [p1==p2] void =
          case+ pf1 of
      | EXP2ind pf1 => let
          prval EXP2ind pf2 = pf2 in exp2_isfun (pf1, pf2)
        end // end of [EXP2ind]
      | EXP2bas () => let
          prval EXP2bas () = pf2 in (* nothing *)
        end // end of [EXP2bas]
    // end of [isfun]

(* ***** ***** *)
(*
** AVL tree in functional form
*)
datatype
avltree_t
  (key:t@ype, value:t@ype, int) =
| AVL_leaf (key, value, 0) of ()
| {hl,hr:nat | ~1 <= hl-hr; hl-hr <= 1}
  AVL_node (key, value, 1+ max (hl, hr)) of
    (key, value, avltree_t (key, value, hl), avltree_t(key, value, hr))
typedef avltree_t (key:t@ype, value:t@ype) = [n:nat] avltree_t(key, value, n)


(* AVL tree height *)
fun
{key:t@ype}{value:t@ype}
height
{h:nat}(
  tree: avltree_t (key, value, h)
): int h =
case+ tree of
| AVL_leaf () => 0
| AVL_node  (_, _, tl, tr) => 1 + max (height (tl), height (tr))

(* AVL tree shortest path *)
fun
{key:t@ype}{value:t@ype}
shortestpath
{h:nat}(
  tree: avltree_t (key, value, h)
): int =
case+ tree of
| AVL_leaf () => 0
| AVL_node (_, _, tl ,tr) => 1+ min (shortestpath(tl), shortestpath(tr))

(* AVL tree size *)
fun
{key:t@ype}{value:t@ype}
size
{h:nat}(
  tree: avltree_t (key, value, h)
): int =
case+ tree of
| AVL_leaf () => 0
| AVL_node (_, _, tl, tr) => 1+ size(tl) + size(tr)

fun
{key:t@ype}{value:t@ype}
isMember
{h:nat}(
  tree: avltree_t (key, value, h), k: key, cmp: (key, key) -> int
): bool =
case+ tree of
| AVL_leaf () => false
| AVL_node  (current, _, tl, tr) =>
    if cmp (current, k) = 0 then true
    else if cmp (current, k) > 0 then isMember (tl, k, cmp)
    else isMember (tr, k, cmp)

fun
{key:t@ype}{value:t@ype}
isEmpty
{h:nat}(
  tree: avltree_t (key, value, h)
): bool =
case+ tree of
| AVL_leaf () => true
| _ => false

(* ***** ***** *)

fun
{key:t@ype}{value:t@ype}
rotate_left
{hl,hr:nat | hr-hl==2}(
  k:key, v:value, tl: avltree_t(key, value, hl), tr:avltree_t(key, value, hr)
): [h:nat | hr <= h; h <= hr+1] avltree_t(key, value, h) = let
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

fun
{key:t@ype}{value:t@ype}
rotate_right
{hl,hr:nat | hl-hr==2}(
  k:key, v:value, tl:avltree_t(key, value, hl), tr:avltree_t(key, value, hr)
): [h:nat | hl <= h; h <= hl+1] avltree_t(key, value, h) = let
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

(* ***** ***** *)

////
fun
{key:t@ype} {value:t@ype}
avltree_insert
(avltree (key, value), key, value, cmp: (key, key) -> int): avltree (key, value)

fun
{key:t@ype} {value:t@ype}
avltree_replace
(avltree (key, value), key, value, cmp: (key, key) -> int): avltree (key, value)

fun
{key:t@ype} {value:t@ype}
avltree_delete
(avltree (key, value), key, cmp: (key, key) -> int): avltree (key, value)

fun
{key:t@ype} {value:t@ype}
avltree_lookup
(avltree (key, value), key, cmp: (key, key) -> int): maybe value

fun
{key:t@ype} {value:t@ype}
avltree_insert_or_replace
(avltree (key, value), key, value, cmp: (key, key) -> int): avltree (key, value)
