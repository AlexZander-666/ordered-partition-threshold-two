import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-123/5,-61/3), (-107/21,-53/11), (-43/21,-85/43), (-1,-63/65), (-47/81,-23/41), (-35/93,-17/47), (-29/99,-7/25)]
private def upperBoxes : Boxes := [(-31,-123/5), (-111/17,-55/9), (-93/35,-23/9), (-37/27,-73/55), (-7/9,-55/73), (-21/43,-41/87), (-33/95,-1/3), (-7/25,-27/101)]

theorem checkedPair2At15 : RootTracking.OrderedPair 7 (row 15 2) (row 17 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
