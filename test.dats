
datasort avl (
  int (*height*), int (*size*) ) =
  | E ( 0, 0)
  | {lh,ls,rh,rs:nat | rh <= lh; lh <= rh+1}
    Bl( 1+lh, 1+ls+rs) of ( int(1+lh), avl ( lh, ls), avl ( rh, rs))
  | {lh,ls,rh,rs:nat | lh <= rh; rh <= lh+1}
    Br( 1+rh, 1+ls+rs) of ( int(1+rh), avl ( lh, ls),  avl ( rh, rs))

// end of [avl]
////
typedef avl_dec (a:t@ype, h:int, s:int) = [h1:nat | h1 <= h; h <= h1+1] avl (a, h1, s)
typedef avl_inc (a:t@ype, h:int, s:int) = [h1:nat | h <= h1; h1 <= h+1] avl (a, h1, s)

typedef avl = [a:t@ype] [h,s:int] avl (a, h, s)

(* ****** ****** *)

extern fun{a:t@ype} avl_size {h,s:nat} (t: avl (a, h, s)): int s

implement{a} avl_size (t) = case+ t of  | Bl (_, _, l, r) => 1 + (avl_size l + avl_size r)
  | Br (_, _, l, r) => 1 + (avl_size l + avl_size r)
  | E () => 0
// end of [avl_size]
