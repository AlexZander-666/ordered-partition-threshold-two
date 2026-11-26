import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-7,-13/3), (-1,-7/9), (-5/11,-1/3)]
private def upperBoxes : Boxes := [(-15,-7), (-5/3,-9/7), (-7/9,-3/5), (-1/3,-3/13)]

theorem checkedPair2At07 : RootTracking.OrderedPair 3 (row 7 2) (row 9 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
