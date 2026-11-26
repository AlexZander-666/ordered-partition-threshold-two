import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-251/5,-1003/21), (-473/39,-945/79), (-107/21,-855/169), (-373/139,-745/279), (-629/395,-157/99), (-129/127,-515/509), (-417/607,-13/19), (-169/343,-337/687), (-279/745,-139/373), (-239/785,-119/393), (-27/101,-215/809)]
private def upperBoxes : Boxes := [(-1007/17,-503/9), (-957/67,-239/17), (-879/145,-439/73), (-391/121,-781/243), (-675/349,-337/175), (-71/57,-567/457), (-469/555,-117/139), (-385/639,-3/5), (-159/353,-317/707), (-67/189,-267/757), (-117/395,-233/791), (-215/809,-107/405)]

theorem checkedPair2At23 : RootTracking.OrderedPair 11 (row 23 2) (row 25 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
