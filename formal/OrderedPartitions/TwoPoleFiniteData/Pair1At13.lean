import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-241/15,-15), (-101/27,-201/55), (-19/13,-151/105), (-107/149,-53/75), (-75/181,-37/91), (-29/99,-57/199)]
private def upperBoxes : Boxes := [(-253/3,-63), (-57/7,-227/29), (-93/35,-185/71), (-139/117,-69/59), (-99/157,-49/79), (-9/23,-71/185), (-57/199,-7/25)]

theorem checkedPair1At13 : RootTracking.OrderedPair 6 (row 13 2) (row 14 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
