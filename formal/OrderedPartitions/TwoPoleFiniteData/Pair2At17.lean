import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-247/9,-123/5), (-111/17,-221/35), (-93/35,-185/71), (-147/109,-73/55), (-7/9,-111/145), (-21/43,-83/173), (-33/95,-65/191), (-7/25,-55/201)]
private def upperBoxes : Boxes := [(-249/7,-31), (-57/7,-227/29), (-99/29,-197/59), (-163/93,-81/47), (-129/127,-1), (-25/39,-99/157), (-39/89,-77/179), (-63/193,-31/97), (-55/201,-27/101)]

theorem checkedPair2At17 : RootTracking.OrderedPair 8 (row 17 2) (row 19 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
