import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-63,-125/3), (-55/9,-109/19), (-21/11,-83/45), (-29/35,-57/71), (-5/11,-39/89), (-15/49,-29/99)]
private def upperBoxes : Boxes := [(-121/7,-15), (-101/27,-25/7), (-19/13,-75/53), (-27/37,-53/75), (-19/45,-37/91), (-29/99,-7/25)]

theorem checkedPair1At12 : RootTracking.OrderedPair 6 (row 12 2) (row 13 2) := by
  apply stay_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
