import JoltTests.DecoderSweep.Main

/-! Entry point for `lake env lean JoltTests/DecoderSweep/Run.lean`, which runs
the comparator with the arguments in `DECODER_SWEEP_ARGS` (see
`JoltTests/DecoderSweep/Main.lean`). -/

#eval show IO Unit from do
  let args := ((← IO.getEnv "DECODER_SWEEP_ARGS").getD "").splitOn " "
  let code ← DecoderSweep.cli (args.filter (!·.isEmpty))
  if code != 0 then throw <| IO.userError s!"decoder-sweep: exit status {code}"
