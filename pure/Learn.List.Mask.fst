module Learn.List.Mask

module T = FStar.Tactics

let rec merge_fun_on_mask_index #src_n mask #b f g (i : nat)
  : Lemma (requires i < src_n)
          (ensures  index (merge_fun_on_mask #src_n mask #b f g) i ==
                   (if index mask i then f i (mask_push #src_n mask i) else g i))
          [SMTPat (index (merge_fun_on_mask #src_n mask #b f g) i)]
  = match mask with
  | true  :: mask ->
          let f' (i : Fin.fin (src_n-1) {index mask i}) (j : Fin.fin (mask_len mask)) = f (i + 1) (j + 1) in
          let g' (i : Fin.fin (src_n-1) {not (index mask i)}) = g (i + 1) in
          assert (merge_fun_on_mask #src_n (true :: mask) f g ==
                  f 0 0 :: merge_fun_on_mask #(src_n-1) mask f' g')
              by (T.trefl ());
          if i > 0 then merge_fun_on_mask_index #(src_n-1) mask f' g' (i - 1)
  | false :: mask ->
          let f' (i : Fin.fin (src_n-1) {index mask i}) (j : Fin.fin (mask_len mask)) = f (i + 1) j in
          let g' (i : Fin.fin (src_n-1) {not (index mask i)}) = g (i + 1) in
          assert (merge_fun_on_mask #src_n (false :: mask) f g ==
                  g 0 :: merge_fun_on_mask #(src_n-1) mask f' g')
              by (T.trefl ());
          if i > 0 then merge_fun_on_mask_index #(src_n-1) mask f' g' (i - 1)

let rec mask_push_pull (#len : nat) (mask : vec len bool) (j : Fin.fin (mask_len mask))
  : Lemma (ensures mask_push mask (mask_pull mask j) = j) (decreases mask)
          [SMTPat (mask_push mask (mask_pull mask j))]
  = match mask with
  | true  :: mask -> if j = 0 then () else mask_push_pull #(len - 1) mask (j - 1)
  | false :: mask -> mask_push_pull #(len - 1) mask j

let rec mask_pull_push (#len : nat) (mask : vec len bool) (i : Fin.fin len {index mask i})
  : Lemma (ensures mask_pull mask (mask_push mask i) = i)
          [SMTPat (mask_pull mask (mask_push mask i))]
  = if i = 0 then ()
    else let b :: mask = mask in
         if b then mask_pull_push #(len-1) mask (i-1)
         else mask_pull_push #(len-1) mask  (i-1)

let rec filter_mask_push (#len : nat) (mask : vec len bool) (i : Fin.fin len {index mask i})
                         (#a : Type) (l : vec len a)
  : Lemma (ensures index (filter_mask mask l) (mask_push mask i) == index l i) (decreases l)
  = if i <> 0
    then let b :: mask = mask in
         let x :: xs   = l    in
         if b then filter_mask_push #(len-1) mask (i-1) xs
         else filter_mask_push #(len-1) mask (i - 1) xs

let filter_mask_map (#a #b : Type) (f : a -> b) (#len : nat) (mask : vec len bool) (l : vec len a)
  = list_extensionality (filter_mask mask (map f l)) (map f (filter_mask mask l)) (fun i -> ())

let rec filter_mask_append #a #len #len' mask mask' l l'
  : Lemma (ensures filter_mask #a #(len+len') (mask@mask') (l@l') == filter_mask mask l @ filter_mask mask' l')
          (decreases l)
  = match mask, l with
  | [], [] -> ()
  | b :: mask, x :: xs -> filter_mask_append #a #(len-1) mask mask' xs l'

let rec filter_mask_true (#a : Type) (#len : nat) (mask : vec len bool) (l : vec len a)
      (tr : (i : Fin.fin len) -> squash (index mask i))
  : Lemma (ensures filter_mask mask l == l) (decreases mask)
  = match mask, l with
  | [], [] -> ()
  | b :: mask, x :: xs -> tr 0; filter_mask_true #a #(len-1) mask xs (fun i -> tr (i+1))

let rec filter_mask_dl_index (#len : nat) (mask : vec len bool) (ts : vec len Type) (xs : Dl.dlist ts) (i : nat)
  : Lemma (requires i < mask_len mask)
          (ensures  Dl.index (filter_mask_dl mask ts xs) i === Dl.index xs (mask_pull mask i))
          (decreases mask)
  = match mask with
  | true :: mask ->
      let t0 :: ts = ts in
      let xs = Dl.DCons?.xs xs in
      if i > 0 then filter_mask_dl_index #(len-1) mask ts xs (i - 1)
  | false :: mask ->
      let t0 :: ts = ts in
      let xs = Dl.DCons?.xs xs in
      filter_mask_dl_index #(len-1) mask ts xs i
