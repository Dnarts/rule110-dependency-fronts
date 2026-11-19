import FiniteBase
namespace Rails.LeftCrystal50
open Rule110Complete Rule110LocalWindow Rule110Fin1320Bridge Rails
set_option exponentiation.threshold 8192
set_option maxRecDepth 200000
set_option maxHeartbeats 0

private def phase (i : Fin 7) : Nat := #[0,1,2,3,4,7,9][i.val]!
private def seed (i : Fin 7) := input 10 576 (phase i)
private def cfg (i : Fin 7) (damaged : Bool) : Config :=
  if damaged then flipZero (line (seed i)) else line (seed i)
private def ringSeed (i : Fin 7) (damaged : Bool) : V :=
  if damaged then defect (seed i) else seed i

private def bg : Array V := #[0xe5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96#5520,
0x72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb#5520,
0xb96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5#5520,
0xdcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72#5520,
0x6e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b9#5520,
0x2dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb7#5520,
0xcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72d#5520]
private def yy : Array V := #[0xe5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5981d87b2e3ec8f2d1f30bec8fbe7c5afb23ec8fb23ecec3f640cb23ec8fb23ec8fb23e3f91f647d91f675dbb23ec8fb23ecebe3ec8fb23ec8fb23ec8c8fb23ec8fb23ec8fb23ec8fb23047dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f6996e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96#5520,
0x72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb7032062cf7d765f647d9cbecf77df647d903161e3e3311f647d91f67647d91f647d91f675f647c7d3f91f647d91f647d9343ec8fb23eb77d9f78fb23ec8fb23ec8fb23ec8fb23eb9c7d91f6418c8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b232e372dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb#5520,
0xb96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5badf5b0fd3efb23d63a19e3323ec11f672c8fb23ec8f8f3f647d91f1962c8fb23ec8fb23ec8c8fb23ec8fb23ec8cec8fafb3da3ec8fb23e5f71f7d91f647d8ebbec8cf659647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97da65b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5#5520,
0xdcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb738fa623f847d91f69b2cf9647d91f6201d91fec8f85f647d91f647d9db8efb23ec8fb7c47d91f19d91f647d91f647d91f5f647c3bec8191f647d91f647d91f46c8fddf647df647d91f647d91f5dac8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b232e372dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72#5520,
0x6e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b968c7183beec8fae347cc2fb2c8fac762c8fadc7d83b23ec8fb23ec80d91c7df64641b23ec8cebec8fb23ec8fb23ec8f8fb23ecf069808fb23ec8fb23ec839f647d9fb23ec8fbec8fb23ec8fb23ecb23ec8c765f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f647647dc7d97d91d91f71f65f6476465c6e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b96e5b9#5520,
0x2dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dd6fad87ebf847c683e3ec9df71f46c3c7c5a64d91f647d9d7d91f647d91f647d919d7ae3ec8fb23ebc059ed1f647c675f1f675f6433b9df647d91f6463b8fb23ec8cb3c38fb23ec8fb2c8dc76406c8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb4cb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb7#5520,
0xcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcbb3a3ecf7d91f646e3efdf647d91ebe9c6ec80647d91f675f647d91f672fb207647d91f647d91f64623ec8fb23fbdf647d91f647d91f647d91f647d91f19df647d91f64641b23ec8fa3647d91f647d91f5f6471f647d6e3b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb23b23ee3ecbec8ec8fb8fb2fb4cb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72dcb72d#5520]

private def snap (i : Fin 7) (d : Bool) : V := (if d then yy else bg)[i.val]!
private theorem snapshots : ∀ i : Fin 7, ∀ d : Bool,
    run 1500 (ringSeed i d) = snap i d := by
  intro idx
  match idx with
  | ⟨0, _⟩ => exact (by decide +kernel : ∀ d : Bool, run 1500 (ringSeed 0 d) = snap 0 d)
  | ⟨1, _⟩ => exact (by decide +kernel : ∀ d : Bool, run 1500 (ringSeed 1 d) = snap 1 d)
  | ⟨2, _⟩ => exact (by decide +kernel : ∀ d : Bool, run 1500 (ringSeed 2 d) = snap 2 d)
  | ⟨3, _⟩ => exact (by decide +kernel : ∀ d : Bool, run 1500 (ringSeed 3 d) = snap 3 d)
  | ⟨4, _⟩ => exact (by decide +kernel : ∀ d : Bool, run 1500 (ringSeed 4 d) = snap 4 d)
  | ⟨5, _⟩ => exact (by decide +kernel : ∀ d : Bool, run 1500 (ringSeed 5 d) = snap 5 d)
  | ⟨6, _⟩ => exact (by decide +kernel : ∀ d : Bool, run 1500 (ringSeed 6 d) = snap 6 d)
  | ⟨k+7, h⟩ => omega

private theorem readAt (i : Fin 7) (d : Bool) (r : Nat) (x : Int)
    (lo : -5520 < x-(r+1500:Nat)) (hi : x+(r+1500:Nat)<5520) :
    evolve (r+1500) (cfg i d) x = line (run r (snap i d)) x := by
  have h : evolve (r+1500) (cfg i d) x =
      evolve (r+1500) (line (ringSeed i d)) x := by
    cases d with
    | false => rfl
    | true => exact (local_obs (seed i) _ _ lo hi).trans (congrFun (line_run _ _) x)
  rw [h,evolve_add,← line_run, snapshots,← line_run]

private theorem bgShift (i : Fin 7) (x : Int) :
    evolve 1510 (line (seed i)) (x-10) = evolve 1500 (line (seed i)) x := by
  have tab : ∀ i : Fin 7, (run 10 (snap i false)).rotateLeft 10 = snap i false := by decide +kernel
  have h := congrArg (fun v : V => v.getLsbD (pos x)) (tab i)
  change ((run 10 (snap i false)).rotateLeft 10).getLsbD (pos x) = _ at h
  rw [BitVec.getLsbD_rotateLeft_of_le (by decide)] at h
  have hh : line (run 10 (snap i false)) (x-10) = line (snap i false) x := by
    unfold line
    split at h
    · rwa [show pos (x-10)=5520-10+pos x by unfold pos at *; omega]
    · simpa only [show decide (pos x < 5520) = true by unfold pos; apply decide_eq_true; omega, Bool.true_and,
        show pos x-10=pos (x-10) by unfold pos at *; omega] using h
  change evolve (10+1500) (line (ringSeed i false)) (x-10) = evolve 1500 (line (ringSeed i false)) x
  rw [evolve_add,← line_run 1500,snapshots,← line_run]
  exact hh

private theorem seedReturn (i : Fin 7) (d : Bool) (x : Int) (hx : x ≤ -199) :
    evolve 1510 (cfg i d) (x-10) = evolve 1500 (cfg i d) x := by
  by_cases h : x < -1500
  · cases d with
    | false => exact bgShift i x
    | true =>
      change evolve 1510 (flipZero _) _ = evolve 1500 (flipZero _) _
      rw [outer _ 1510 _ (Or.inl (by omega)),outer _ 1500 _ (Or.inl (by omega))]
      exact bgShift i x
  · have tab : ∀ i : Fin 7, ∀ b : Bool,
          (run 10 (snap i b)).extractLsb' 1250 1302 = (snap i b).extractLsb' 1260 1302 := by decide +kernel
    let k := (x+1500).toNat
    have hk : k<1302 := by dsimp [k]; omega
    have hh := congrArg (fun v : BitVec 1302 => v.getLsbD k) (tab i d)
    simp only [BitVec.getLsbD_extractLsb',hk,decide_true,Bool.true_and] at hh
    rw [readAt i d 10 _ (by omega) (by omega),readAt i d 0 _ (by omega) (by omega)]
    simpa only [run, line,show pos (x-10)=1250+k by dsimp [pos,k]; omega,
      show pos x=1260+k by dsimp [pos,k]; omega] using hh

private theorem repeatAt (i : Fin 7) (d : Bool) (n : Nat) (x : Int) (hx : x ≤ -199-(n:Int)) :
    evolve (n+1510) (cfg i d) (x-10) = evolve (n+1500) (cfg i d) x := by
  have h := evolve_agree_window n (shift 10 (evolve 1510 (cfg i d)))
    (evolve 1500 (cfg i d)) x (fun j _ hj => seedReturn i d j (by omega))
  rw [evolve_shift] at h
  simpa only [shift, evolve_add n 1510, evolve_add n 1500] using h

private def bit (i : Fin 7) (d : Bool) (r : Fin 10) (k : Fin 1282) :=
  line (run r.val (snap i d)) (-(1500+(r.val:Int))+20+k.val)

private theorem coverage : ∀ r : Fin 10, ∀ k : Fin 1282, ∃ i : Fin 7,
    bit i false r k ≠ bit i true r k := by
  intro r k
  let zs := List.ofFn (fun i : Fin 7 => (run r.val (snap i false),run r.val (snap i true)))
  have tab : ∀ q : Fin 10, (Finite.diff (List.ofFn (fun i : Fin 7 =>
      (run q.val (snap i false), run q.val (snap i true))))).extractLsb' (1280-q.val) 1282 =
      BitVec.allOnes 1282 := by decide +kernel
  have hh := congrArg (fun v : BitVec 1282 => v.getLsbD k.val) (tab r)
  simp only [BitVec.getLsbD_extractLsb',k.isLt,decide_true,Bool.true_and,BitVec.getLsbD_allOnes] at hh
  have hit := Finite.hit (zs:=zs) hh
  obtain ⟨z,hz,hd⟩ := hit
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hz
  subst z
  exact ⟨i,by simpa only [bit,line,show pos (-(1500+(r.val:Int))+20+k.val)=1280-r.val+k.val by unfold pos; omega] using hd⟩

private theorem transport (i : Fin 7) (d : Bool) (r : Fin 10) (k : Fin 1282) (q : Nat) :
    let t := 1500+r.val+10*q
    evolve t (cfg i d) (-(t:Int)+20+k.val) = bit i d r k := by
  dsimp only
  induction q with
  | zero =>
    simp only [Nat.mul_zero,Nat.add_zero]
    rw [Nat.add_comm 1500 r.val,readAt i d r.val _ (by omega) (by omega)]
    unfold bit
    rw [show -((r.val+1500:Nat):Int)+20+k.val = -(1500+(r.val:Int))+20+k.val by omega]
  | succ q ih =>
    have h := repeatAt i d (r.val+10*q) (-((1500+r.val+10*q:Nat):Int)+20+k.val) (by omega)
    rw [show 1500+r.val+10*(q+1)=(r.val+10*q)+1510 by omega,
      show -(((r.val+10*q)+1510:Nat):Int)+20+k.val =
        (-((1500+r.val+10*q:Nat):Int)+20+k.val)-10 by omega, h,
      show r.val+10*q+1500=1500+r.val+10*q by omega]
    exact ih

theorem left_strip (t : Nat) (ht : 1500 ≤ t) (k : Int) (hk : 20 ≤ k) (hk' : k ≤ 1301) :
    Rule110KernelCert.EssentialAt t ((t:Int)-k) := by
  let r : Fin 10 := ⟨(t-1500)%10,by omega⟩
  let j : Fin 1282 := ⟨(k-20).toNat,by omega⟩
  let q := (t-1500)/10
  have ht' : 1500+r.val+10*q=t := by dsimp [r,q]; omega
  have hk'' : 20+(j.val:Int)=k := by dsimp [j]; omega
  obtain ⟨i,hi⟩ := coverage r j
  have he (d : Bool) := transport i d r j q
  change ∀ d : Bool, evolve (1500+r.val+10*q) (cfg i d)
    (-((1500+r.val+10*q:Nat):Int)+20+j.val) = bit i d r j at he
  rw [ht'] at he
  have hx : -(t:Int)+20+j.val = -(t:Int)+k := by omega
  rw [hx] at he
  have e := essential (line (seed i)) t (-(t:Int)+k)
    (show evolve t (cfg i false) _ ≠ evolve t (cfg i true) _ by rw [he false,he true]; exact hi)
  simpa only [show -(-(t:Int)+k)=(t:Int)-k by omega] using e

#print axioms left_strip
end Rails.LeftCrystal50
