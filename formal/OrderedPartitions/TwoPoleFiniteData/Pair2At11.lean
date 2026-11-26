import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-59/5,-117/11), (-93/35,-23/9), (-1,-63/65), (-21/43,-41/87), (-15/49,-29/99)]
private def upperBoxes : Boxes := [(-121/7,-15), (-101/27,-25/7), (-19/13,-75/53), (-27/37,-53/75), (-19/45,-37/91), (-29/99,-7/25)]

theorem checkedPair2At11 : RootTracking.OrderedPair 5 (row 11 2) (row 13 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
