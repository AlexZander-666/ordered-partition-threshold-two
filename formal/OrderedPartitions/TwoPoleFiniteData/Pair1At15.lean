import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-31,-61/3), (-27/5,-53/11), (-43/21,-21/11), (-1,-31/33), (-3/5,-23/41), (-9/23,-17/47), (-15/49,-7/25)]
private def upperBoxes : Boxes := [(-1679376855628213,-63), (-59/5,-29/3), (-25/7,-49/15), (-5/3,-39/25), (-15/17,-29/35), (-11/21,-21/43), (-17/47,-1/3), (-7/25,-13/51)]

theorem checkedPair1At15 : RootTracking.OrderedPair 7 (row 15 2) (row 16 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
