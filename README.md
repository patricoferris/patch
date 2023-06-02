Patch
-----

*Status: Experimental & Very WIP*

Diffing OCaml values via [runtime types](https://github.com/dbuenzli/typegist).

First a type with a runtime type.

```ocaml
# type t = { age : int; height : int }
type t = { age : int; height : int; }
# let t =
  let open Typegist.Type.Gist in
  let age = field "age" int (fun p -> p.age) in
  let height = field "height" int (fun p -> p.height) in
  let v age height = { age; height } in
  record "t" @@ (ctor v * age * height)
val t : t Typegist.Type.Gist.t = Typegist.Type.Gist.Record <abstr>
```

Then some values.

```ocaml
let v0 = { age = 0; height = 0 }
let v1 = { age = 2; height = 0 }
let v2 = { age = 0; height = 2 }
```

And now for some diffing.

```ocaml
# let p1 = Patch.diff t v0 v1;;
val p1 : t Patch.t = <abstr>
# let p2 = Patch.diff t v0 v2;;
val p2 : t Patch.t = <abstr>
# let p = List.fold_left Patch.join Patch.empty [p1; p2];;
val p : t Patch.t = <abstr>
# Patch.apply p v0
- : t = {age = 2; height = 2}
```

