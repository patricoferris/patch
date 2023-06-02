type info = { age : int; height : int }
let info =
  let open Typegist.Type.Gist in
  let age = field "age" int (fun p -> p.age) in
  let height = field "height" int (fun p -> p.height) in
  let v age height = { age; height } in
  record "info" @@ (ctor v * age * height)

type t = { info : info }

let t =
  let open Typegist.Type.Gist in
  let info = field "info" info (fun p -> p.info) in
  let v info = { info } in
  record "t" @@ (ctor v * info)

let () =
  let v0 = { info = { age = 0; height = 0 }} in
  let v1 = { info = { age = 2; height = 0 }} in
  let v2 = { info = { age = 0; height = 2 }} in
  let d1 = Patch.diff t v0 v1 in
  let d2 = Patch.diff t v0 v2 in
  let diff = List.fold_left Patch.join Patch.empty [ d1; d2 ] in
  let e = Patch.apply diff v0 in
  assert (e = { info = { age = 2; height = 2 }})
