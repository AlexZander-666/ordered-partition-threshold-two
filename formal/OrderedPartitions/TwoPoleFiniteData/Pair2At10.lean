import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-125/3,-31), (-103/25,-51/13), (-71/57,-35/29), (-45/83,-11/21), (-31/97,-15/49)]
private def upperBoxes : Boxes := [(-63,-125/3), (-55/9,-109/19), (-21/11,-83/45), (-29/35,-57/71), (-5/11,-39/89), (-15/49,-29/99)]

theorem checkedPair2At10 : RootTracking.OrderedPair 5 (row 10 2) (row 12 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
