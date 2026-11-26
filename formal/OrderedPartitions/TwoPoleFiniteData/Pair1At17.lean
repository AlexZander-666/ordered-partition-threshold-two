import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-247/9,-123/5), (-111/17,-221/35), (-93/35,-185/71), (-147/109,-73/55), (-7/9,-111/145), (-21/43,-83/173), (-33/95,-65/191), (-7/25,-55/201)]
private def upperBoxes : Boxes := [(-127,-253/3), (-239/17,-119/9), (-105/23,-209/47), (-87/41,-173/83), (-137/119,-17/15), (-105/151,-13/19), (-81/175,-5/11), (-65/191,-1/3), (-55/201,-27/101)]

theorem checkedPair1At17 : RootTracking.OrderedPair 8 (row 17 2) (row 18 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
