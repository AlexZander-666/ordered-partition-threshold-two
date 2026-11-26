import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-31,-15), (-23/9,-11/5), (-7/9,-13/19), (-9/23,-1/3)]
private def upperBoxes : Boxes := [(-29/3,-7), (-5/3,-19/13), (-13/19,-3/5), (-1/3,-7/25)]

theorem checkedPair1At08 : RootTracking.OrderedPair 4 (row 8 2) (row 9 2) := by
  apply stay_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
