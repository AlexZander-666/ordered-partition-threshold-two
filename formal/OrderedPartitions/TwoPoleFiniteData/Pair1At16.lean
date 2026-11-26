import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-507/5,-253/3), (-117/11,-467/45), (-199/57,-397/115), (-79/49,-315/197), (-119/137,-237/275), (-11/21,-175/337), (-135/377,-67/189), (-7/25,-111/401)]
private def upperBoxes : Boxes := [(-247/9,-493/19), (-111/17,-443/69), (-93/35,-371/141), (-147/109,-293/219), (-223/289,-111/145), (-21/43,-167/345), (-131/381,-65/191), (-111/401,-55/201)]

theorem checkedPair1At16 : RootTracking.OrderedPair 8 (row 16 2) (row 17 2) := by
  apply stay_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
