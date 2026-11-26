import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-63,-125/3), (-55/9,-109/19), (-21/11,-83/45), (-29/35,-57/71), (-5/11,-39/89), (-15/49,-29/99)]
private def upperBoxes : Boxes := [(-127,-63), (-57/7,-113/15), (-93/35,-23/9), (-35/29,-69/59), (-25/39,-49/79), (-9/23,-35/93), (-29/99,-7/25)]

theorem checkedPair2At12 : RootTracking.OrderedPair 6 (row 12 2) (row 14 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
