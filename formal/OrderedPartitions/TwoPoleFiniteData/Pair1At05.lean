import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-3,-11/5), (-3/5,-5/11)]
private def upperBoxes : Boxes := [(-15,-7), (-5/3,-9/7), (-5/11,-1/3)]

theorem checkedPair1At05 : RootTracking.OrderedPair 2 (row 5 2) (row 6 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
