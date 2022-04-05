module Learn.LowStar.Queue.Prop

module M   = LowStar.Modifies

let live_seg = live_seg_def

let live_seg_unfold #c a = assert_norm (live_seg a == live_seg_def a)

let rec loc_seg_live_in #c a h sg =
  match sg.segment with
  | []    -> ()
  | _ :: _ -> loc_seg_live_in a h (tail_seg sg)

let rec loc_seg_cell #c sg x =
  match sg with
  | [] -> ()
  | hd :: tl -> eliminate x == hd \/ L.memP x tl
                returns M.(loc_seg sg `loc_includes` loc_buffer x)
                   with pf_hd. ()
                    and pf_tl. loc_seg_cell tl x

let rec live_seg_cell #c a h sg x =
  match sg.segment with
  | [] -> ()
  | hd :: tl -> eliminate x == hd \/ L.memP x tl
                returns B.live h x
                   with pf_hd. ()
                    and pf_tl. live_seg_cell a h (tail_seg sg) x

let rec frame_seg #c a h0 h1 sg r =
  match sg.segment with
  | []    -> ()
  | _ :: _ -> frame_seg a h0 h1 (tail_seg sg) r

let rec frame_seg_mod_data #c a h0 h1 sg =
  match sg.segment with
  | []    -> ()
  | _ :: _ -> frame_seg_mod_data a h0 h1 (tail_seg sg)

let rec disjoint_mod_next_seg #c a h0 h1 p sg
  = match sg.segment with
    | [] -> ()
    | _ :: _ -> disjoint_mod_next_seg a h0 h1 p (tail_seg sg)

let rec append_seg_live #c a h sg0 sg1 =
  match sg0.segment with
  | [] -> ()
  | _ :: _ -> append_seg_live a h (tail_seg sg0) sg1

let rec last_cell_live #c a h sg =
  match sg.segment with
  | []  -> ()
  | [_] -> ()
  | _ :: _ -> last_cell_live a h (tail_seg sg)

let empty_live #c a exit h = ()

let sg_mkcons_lem #c a h hd tl = ()

let sg_uncons_lem #c a h sg = ()

let entry_null_is_empty #c a h sg =
  B.null_unique (sg_entry sg)

let list_nil_entry_nnull #c a h sg = ()

inline_for_extraction
let sgn_entry #c a p sg = p

inline_for_extraction
let sg_next #c a get_next p sg = get_next (p.(0ul))
