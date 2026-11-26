import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-53/11,-13/3), (-1,-31/33), (-9/23,-17/47)]
private def upperBoxes : Boxes := [(-31,-61/3), (-23/9,-45/19), (-7/9,-27/37), (-17/47,-1/3)]

theorem checkedPair1At07 : RootTracking.OrderedPair 3 (row 7 2) (row 8 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
