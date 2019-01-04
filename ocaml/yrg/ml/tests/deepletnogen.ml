let f = fun x ->
  (fun y ->
   let g = (fun z -> y) y in
   g)
in
  f 0 0
