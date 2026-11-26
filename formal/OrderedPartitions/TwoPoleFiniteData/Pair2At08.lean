import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-31,-15), (-23/9,-11/5), (-7/9,-13/19), (-9/23,-1/3)]
private def upperBoxes : Boxes := [(-42833083,-31), (-13/3,-25/7), (-9/7,-17/15), (-3/5,-11/21), (-1/3,-7/25)]

theorem checkedPair2At08 : RootTracking.OrderedPair 4 (row 8 2) (row 10 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
