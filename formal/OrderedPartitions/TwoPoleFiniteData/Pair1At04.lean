import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-7,-27/5), (-3/5,-11/21)]
private def upperBoxes : Boxes := [(-23/9,-11/5), (-11/21,-5/11)]

theorem checkedPair1At04 : RootTracking.OrderedPair 2 (row 4 2) (row 5 2) := by
  apply stay_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
