- Make `many` total (`%default total`, `covering` where needed)
- Proof `(a, b : Char) -> c = char a <|> char b -> Either (c = a) (c = b)`,
  maybe even generalize it for all `Alternative` `ParserT`-s
- Use `List1` in `sepBy1` and other places
- Return from `ParserT str m t` not just `t`, but `(t, Position)` ?
- Errors' position needs to be a range (e.g. `row:from-to`)
