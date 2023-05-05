type ('a, 'b) either =
  | Left of 'a
  | Right of 'b

let fold_lefti f acc xs =
  snd (List.fold_left (fun (i, acc) x -> (i + 1, f i acc x)) (0, acc) xs)

let fold_righti f xs acc =
  snd (List.fold_right (fun x (i, acc) -> (i + 1, f i x acc)) xs (0, acc))
