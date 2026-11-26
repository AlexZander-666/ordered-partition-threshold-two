import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-57/7,-7), (-5/3,-39/25), (-25/39,-3/5), (-1/3,-15/49)]
private def upperBoxes : Boxes := [(-59/5,-29/3), (-47/17,-23/9), (-1,-31/33), (-21/43,-5/11), (-15/49,-7/25)]

theorem checkedPair2At09 : RootTracking.OrderedPair 4 (row 9 2) (row 11 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
