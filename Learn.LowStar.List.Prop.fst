module Learn.LowStar.List.Prop

let live_seg = live_seg_def

let live_seg_unfold a = assert_norm (live_seg #a == live_seg_def #a)

(** Lemmes sur les prédicats *)

let rec loc_seg_live_in #a h sg
  = match sg.segment with
    | [] -> ()
    | _ :: _ -> loc_seg_live_in h (tail_seg sg)

let rec loc_addr_seg_live_in #a h sg
  = match sg.segment with
    | [] -> ()
    | _ :: _ -> loc_addr_seg_live_in h (tail_seg sg)

let rec frame #a h0 h1 sg r
  = match sg.segment with
    | [] -> ()
    | hd :: tl -> frame h0 h1 (tail_seg sg) r

(** Manipulation des segments *)

let empty_live a h = ()

let sg_mkcons_lem #a h hd sg = ()

let sg_uncons_lem #a h sg = ()

let list_nil_entry_live (#a : Type0) (h : HS.mem) (sg : list_nil a)
  : Lemma (requires live_seg h sg)
          (ensures  B.live h (entry sg))
  = ()

let list_seg_Cons_entry_live (#a : Type0) (h : HS.mem) (sg : list_seg a)
  : Lemma (requires live_seg h sg /\ Cons? sg.segment)
          (ensures  B.live h (entry sg))
  = ()

let entry_null_is_empty #a h sg = ()

let list_nil_entry_nnull #a h sg = ()

inline_for_extraction
let sgn_entry #a p sg = p

inline_for_extraction
let sg_next #a p sg = (p.(0ul)).next

(** opérations *)

let rec append_seg_live #a h sg0 sg1
  = match sg0.segment with
    | [] -> ()
    | _ :: _ -> append_seg_live h (tail_seg sg0) sg1
