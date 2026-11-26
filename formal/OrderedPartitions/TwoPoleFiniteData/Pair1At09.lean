import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-57/7,-113/15), (-5/3,-79/49), (-49/79,-3/5), (-1/3,-31/97)]
private def upperBoxes : Boxes := [(-125/3,-31), (-103/25,-51/13), (-71/57,-35/29), (-45/83,-11/21), (-31/97,-15/49)]

theorem checkedPair1At09 : RootTracking.OrderedPair 4 (row 9 2) (row 10 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
