import MathQL.Result

namespace MathQL

/-- MathQL integers have the same range in SQL and postprocessing. -/
def integerInRange (n : Int) : Bool :=
  -9223372036854775808 ≤ n && n ≤ 9223372036854775807

def checkedInteger (n : Int) : Result Int :=
  if integerInRange n then .ok n else .error "integer overflow: outside signed 64-bit range"

end MathQL
