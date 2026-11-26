import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-63,-31), (-13/3,-51/13), (-9/7,-35/29), (-23/41,-11/21), (-1/3,-15/49)]
private def upperBoxes : Boxes := [(-59/5,-29/3), (-47/17,-23/9), (-1,-31/33), (-21/43,-5/11), (-15/49,-7/25)]

theorem checkedPair1At10 : RootTracking.OrderedPair 5 (row 10 2) (row 11 2) := by
  apply stay_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
