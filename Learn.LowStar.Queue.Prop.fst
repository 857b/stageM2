module Learn.LowStar.Queue.Prop

let live_seg = live_seg_def

let live_seg_unfold a = assert_norm (live_seg #a == live_seg_def #a)

let rec loc_seg_live_in #a h sg =
  match sg.segment with
  | []    -> ()
  | _ :: _ -> loc_seg_live_in h (tail_seg sg)

let rec frame_seg #a h0 h1 sg r =
  match sg.segment with
  | []    -> ()
  | _ :: _ -> frame_seg h0 h1 (tail_seg sg) r

let rec disjoint_mod_next_seg #a h0 h1 p sg
  = match sg.segment with
    | [] -> ()
    | _ :: _ -> disjoint_mod_next_seg h0 h1 p (tail_seg sg)

let rec append_seg_live #a h sg0 sg1 =
  match sg0.segment with
  | [] -> ()
  | _ :: _ -> append_seg_live h (tail_seg sg0) sg1

let rec last_cell_live #a h sg =
  match sg.segment with
  | []  -> ()
  | [_] -> ()
  | _ :: _ -> last_cell_live h (tail_seg sg)

let empty_live #a exit h = ()

let sg_mkcons_lem #a h hd tl = ()

let sg_uncons_lem #a h sg = ()

let entry_null_is_empty #a h sg =
  B.null_unique (sg_entry sg)

let list_nil_entry_nnull #a h sg = ()

inline_for_extraction
let sgn_entry #a p sg = p

inline_for_extraction
let sg_next #a p sg = (p.(0ul)).next
