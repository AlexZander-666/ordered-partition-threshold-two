import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-15,-29/3), (-19/13,-9/7), (-5/11,-9/23)]
private def upperBoxes : Boxes := [(-27/5,-13/3), (-1,-15/17), (-9/23,-1/3)]

theorem checkedPair1At06 : RootTracking.OrderedPair 3 (row 6 2) (row 7 2) := by
  apply stay_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
