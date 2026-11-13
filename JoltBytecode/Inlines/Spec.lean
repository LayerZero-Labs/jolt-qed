import JoltBytecode.Inlines.Sha256.Spec
import JoltBytecode.Inlines.Keccak256.Spec
import JoltBytecode.Inlines.Blake2b.Spec

/-!
# Specifications of Jolt's hash inlines

This module imports the specifications of Jolt's five hash inlines, copied from EthLib at commit
`5310b3ec007b05a2bfe33b01125392b07df5f636` (`docs/inline-precompiles.md`, section 5.6):

- `SHA256` and `SHA256_INIT`: `JoltSpec.Sha256.Spec.compression`, with
  `JoltSpec.Sha256.Spec.initial` for `SHA256_INIT`;
- `KECCAK256` and `KECCAK256_ABSORB_PERMUTE`: `JoltSpec.Keccak.keccakF`, after
  `JoltSpec.Keccak.Internal.absorbBlock 136` for `KECCAK256_ABSORB_PERMUTE`;
- `BLAKE2`: `JoltSpec.Blake2b.Spec.compress 12`.

The known-answer tests are in the `JoltTests` library (`JoltTests/InlineKat/`).
-/
