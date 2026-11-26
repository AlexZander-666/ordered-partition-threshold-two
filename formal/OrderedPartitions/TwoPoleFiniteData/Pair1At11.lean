import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-59/5,-235/21), (-185/71,-23/9), (-127/129,-63/65), (-21/43,-83/173), (-15/49,-59/197)]
private def upperBoxes : Boxes := [(-63,-251/5), (-219/37,-109/19), (-167/89,-83/45), (-29/35,-115/141), (-79/177,-39/89), (-59/197,-29/99)]

theorem checkedPair1At11 : RootTracking.OrderedPair 5 (row 11 2) (row 12 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
