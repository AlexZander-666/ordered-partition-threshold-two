import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-63,-503/9), (-479/33,-239/17), (-55/9,-439/73), (-391/121,-195/61), (-169/87,-337/175), (-71/57,-283/229), (-235/277,-117/139), (-193/319,-3/5), (-159/353,-79/177), (-67/189,-133/379), (-117/395,-29/99), (-27/101,-107/405)]
private def upperBoxes : Boxes := [(-505/7,-63), (-483/29,-241/15), (-449/63,-7), (-203/53,-405/107), (-357/155,-89/39), (-307/205,-153/103), (-259/253,-129/127), (-27/37,-215/297), (-45/83,-179/333), (-151/361,-75/181), (-65/191,-129/383), (-29/99,-115/397), (-107/405,-53/203)]

theorem checkedPair2At25 : RootTracking.OrderedPair 12 (row 25 2) (row 27 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
