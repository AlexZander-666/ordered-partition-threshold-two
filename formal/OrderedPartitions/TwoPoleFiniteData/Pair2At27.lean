import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-505/7,-1009/15), (-483/29,-965/59), (-449/63,-897/127), (-203/53,-811/213), (-357/155,-713/311), (-613/411,-153/103), (-517/507,-129/127), (-431/593,-215/297), (-359/665,-179/333), (-151/361,-301/723), (-65/191,-259/765), (-231/793,-115/397), (-107/405,-213/811)]
private def upperBoxes : Boxes := [(-253/3,-1011/13), (-487/25,-973/51), (-457/55,-913/111), (-209/47,-835/189), (-187/69,-747/277), (-327/185,-653/371), (-281/231,-561/463), (-119/137,-475/549), (-401/623,-25/39), (-339/685,-169/343), (-289/735,-9/23), (-253/771,-63/193), (-57/199,-227/797), (-213/811,-53/203)]

theorem checkedPair2At27 : RootTracking.OrderedPair 13 (row 27 2) (row 29 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
