module

public import LeanTex.Cli.SlotLoss
import all LeanTex.Cli.SlotLoss

/-! The legacy font tests read the wording through this modern test module. -/

namespace Tests.SlotLossWording

open LeanTex.Cli

public def servedWords (served : SlotLoss.Served) : String := served.words

public def artifactWord (artifact : Emit) : String := SlotLoss.artifactWord artifact

public def carryOnly (carry : SlotLoss.Carry) : Option String := carry.only

end Tests.SlotLossWording
